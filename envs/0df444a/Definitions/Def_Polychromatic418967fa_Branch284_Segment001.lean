-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch284_Segment001
-- name    : Polychromatic418967fa_Branch284_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:57:55.488732+00:00
-- url     : https://prove2.me/theorems/569fefc0-58cd-4189-9130-48a78e36e7de
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch284_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_284_segment_001 : allB 182 284 :=
  allB_succ' 104 181 284 (Eq.refl Bool.true) (allA_of_3_0 104 181 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 105 180 284 (Eq.refl Bool.true) (allA_succ_of_gcd 104 180 284 4 26 45 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 180 284 (accept_3_2 103 180 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 180 284 2 51 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 180 284 (Polychromatic418967fa.accept_11_2_4_9_1_484
  101 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 180 284 4 25 45 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 180 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 99 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 180 284 2 49 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 180 284 (accept_3_2 97 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 180 284 4 24 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 180 284 (Polychromatic418967fa.accept_16_15_4_12_1_2731 95 180 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 180 284 2 47 90 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 180 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 93 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 180 284 4 23 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 180 284 (accept_3_2 91 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 180 284 2 45 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 180 284 (Polychromatic418967fa.accept_16_9_4_12_1_4896 89 180 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 180 284 4 22 45 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 180 284
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 87 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 180 284 2 43 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 180 284 (accept_3_2 85 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 180 284 4 21 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 180 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 180 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 180 284 2 41 90 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 180 284
  (Polychromatic418967fa.accept_16_1_4_12_1_376 81 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 180 284 4 20 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 180 284 (accept_3_2 79 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 180 284 2 39 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 180 284 (Polychromatic418967fa.accept_16_13_4_12_1_1805 77 180 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 180 284 4 19 45 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 180 284
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 75 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 180 284 2 37 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 180 284 (accept_3_2 73 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 180 284 4 18 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 180 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 180 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 180 284 2 35 90 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 180 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 180 284 4 17 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 180 284 (accept_3_2 67 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 284 2 33 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 180 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 180 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 180 284 4 16 45 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 180 284
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 180 284 2 31 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 180 284 (accept_3_2 61 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 284 4 15 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 180 284 (Polychromatic418967fa.accept_16_11_4_12_1_1760 59 180 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 284 2 29 90 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 180 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 180 284 4 14 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 180 284 (accept_3_2 55 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 180 284 2 27 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 180 284 (Polychromatic418967fa.accept_16_5_4_12_1_3800 53 180 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 284 4 13 45 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 180 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 180 284 2 25 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 180 284 (accept_3_2 49 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 284 4 12 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 284 (Polychromatic418967fa.accept_16_15_4_12_1_2731 47 180 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 284 2 23 90 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 180 284
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 180 284 4 11 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 180 284 (accept_3_2 43 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 284 2 21 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 180 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 284 4 10 45 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 180 284
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 180 284 2 19 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 180 284 (accept_3_2 37 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 284 4 9 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 180 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 180 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 284 2 17 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 284 (Polychromatic418967fa.accept_16_1_4_12_1_376
  33 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 180 284 4 8 45 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 284
  (accept_3_2 31 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 180 284 2 15 90 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 180 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 180 284 4 7 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 180 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 180 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 180 284 2 13 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 284 (accept_3_2 25 180 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 180 284 4 6 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 180 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 284 2 11 90 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 284
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 180 284 4 5 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 180 284 (accept_3_2 19 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  180 284 2 9 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 180 284 (Polychromatic418967fa.accept_16_1_4_12_1_376 17 180 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 284 4 4 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 180 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 284 2 7 90 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 284 (accept_3_2 13
  180 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 284 4 3 45 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 284
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 180 284 2 5 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 180 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 180 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 284 4 2 45 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 284 (accept_3_2 7 180 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 284 2 3 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 284 (Polychromatic418967fa.accept_16_5_4_12_1_3800
  5 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 284 4 1 45 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 284
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 180 284 2 1 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 180 284 (accept_3_2 1 180 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 179 284 (Eq.refl Bool.true) (allA_succ_of_accept 105 179 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 105 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 179 284 (Polychromatic418967fa.accept_16_8_3_12_1_1819 104 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 179 284 (accept_3_2 103 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 179 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 179 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 101 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 179 284 (accept_3_2 100 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 179 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 98 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 179 284 (accept_3_2 97 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 179 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 179 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 95 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 179 284 (accept_3_2 94 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 179 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 92 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 179 284 (accept_3_2 91 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 179 284 (Polychromatic418967fa.accept_13_12_10_11_1_1279 90 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 179 284
  (Polychromatic418967fa.accept_16_9_3_12_1_1802 89 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 179 284 (accept_3_2 88 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 179 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 86 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 179 284 (accept_3_2 85 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 179 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 179 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 179 284 (accept_3_2 82 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 179 284 (Polychromatic418967fa.accept_13_2_10_11_1_1276 80 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 179 284 (accept_3_2 79 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 179 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 179 284
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 77 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 179 284 (accept_3_2 76 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 179 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 179 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 179 284 (accept_3_2 73 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 179 284 (Polychromatic418967fa.accept_11_6_3_9_1_906
  72 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 179 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 179 284 (accept_3_2 70 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 179 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 68 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 179 284 (accept_3_2 67 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 179 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 179 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 179 284 (accept_3_2 64 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 179 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 179 284 (accept_3_2 61 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 179 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 179 284
  (Polychromatic418967fa.accept_23_13_18_8_1_9457 59 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 179 284 (accept_3_2 58 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 179 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 179 284 (accept_3_2 55 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 179 284
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 54 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 53 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 284 (accept_3_2 52 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 284
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 179 284 (accept_3_2 49 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 179 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 179 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 284 (accept_3_2 46 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 284
  (Polychromatic418967fa.accept_25_19_4_9_1_15812 44 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 179 284 (accept_3_2 43 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 179 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 179 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 284 (Polychromatic418967fa.accept_13_2_10_11_1_1276 41 179
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 284 (accept_3_2 40 179
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 179 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 179 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 284 (accept_3_2 37 179 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 179 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 284
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 179 284 (accept_3_2 34 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 179 284 (Polychromatic418967fa.accept_19_13_8_18_1_10905 32 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 284 (accept_3_2 31 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 284 (accept_3_2 28 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 284 (accept_3_2 25 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 284 (accept_3_2 22 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 284 (accept_3_2 19 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 284
  (Polychromatic418967fa.accept_11_6_3_9_1_906 17 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 284 (accept_3_2 16 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 284 (accept_3_2 13 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 179 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 284 (accept_3_2 10 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 284 (accept_3_2 7 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 179 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 284
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 284 (accept_3_2 4 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 284 (accept_3_2 1 179 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 178 284 (Eq.refl Bool.true) (allA_of_3_0 107 178 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 177 284 (Eq.refl Bool.true) (allA_succ_of_accept 107 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 177 284 (accept_3_2 106 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 177 284 (Polychromatic418967fa.accept_13_1_8_11_1_724 105 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 177 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 104 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 177 284 (accept_3_2 103 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 177 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 177
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 177 284 (accept_3_2 100 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 177 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 99 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 177 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 177 284 (accept_3_2 97 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 177 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 177 284 (accept_3_2 94 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 177 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 93 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 177 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 177 284 (accept_3_2 91 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 177 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 177 284 (accept_3_2 88 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 177 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 87 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 177 284 (Polychromatic418967fa.accept_14_2_9_4_1_1735 86 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 177 284 (accept_3_2 85 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 177 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 177 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 177 284 (accept_3_2 82 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 177 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 81 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 177 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 177 284 (accept_3_2 79 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 177 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 177 284 (accept_3_2 76 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 177 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 177 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 284 (accept_3_2 73 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 177 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 177 284 (accept_3_2 70 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 177 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 177 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 177 284 (accept_3_2 67 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 177 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 177 284 (accept_3_2 64 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 177 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 177 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 284 (accept_3_2 61 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 177 284 (Polychromatic418967fa.accept_19_3_6_18_1_2665 60 177 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 177 284 (accept_3_2 58 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 177 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 177 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 284 (accept_3_2 55 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 177 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 177 284 (accept_3_2 52 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 177 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 51 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 177 284 (Polychromatic418967fa.accept_16_2_1_12_1_3798 50 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 284 (accept_3_2 49 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 177 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 177 284 (accept_3_2 46 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 177 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 177 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 284 (accept_3_2 43 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 284 (accept_3_2 40 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 177 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 177 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 284 (accept_3_2 37 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 284 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 177 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 284 (accept_3_2 34 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 284 (accept_3_2 31 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 177 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 284 (accept_3_2 28 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 284 (accept_3_2 25 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 177 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 284 (accept_3_2 22 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 284 (accept_3_2 19 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 284 (accept_3_2 16 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 284 (Polychromatic418967fa.accept_21_15_9_11_1_5417 15 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 284 (Polychromatic418967fa.accept_13_1_8_11_1_724 14 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 284 (accept_3_2 13 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 177 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 284 (accept_3_2 10 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 284 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 284 (accept_3_2 7 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 177 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 284 (accept_3_2 4 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 177 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 284 (accept_3_2 1 177 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 176 284 (Eq.refl Bool.true) (allA_succ_of_gcd 108 176 284 4 27 44 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 176 284
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 107 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 176 284 2 53 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 176 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 105 176 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 176 284 4 26 44 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 176 284 (accept_3_2 103 176 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 176 284 2 51 88 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 176 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 101 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 176 284 4 25 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 176 284 (Polychromatic418967fa.accept_19_4_5_18_1_6647 99 176 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 176 284 2 49 88 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 176 284 (accept_3_2 97 176 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 176 284 4 24 44 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 176 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 95 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 176 284 2 47 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 176 284 (Polychromatic418967fa.accept_15_3_11_14_1_1705 93 176 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 176 284 4 23 44 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 176 284 (accept_3_2 91 176 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 176 284 2 45 88 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 176 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 89 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 176 284 4 22 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 176 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 176 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 176 284 2 43 88 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 176 284 (accept_3_2 85 176 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 176 284 4 21 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 176 284 (Polychromatic418967fa.accept_13_5_7_11_1_3470
  83 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 176 284 2 41 88 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 176 284
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 81 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 176 284 4 20 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 176 284 (accept_3_2 79 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 176 284 2 39 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 176 284 (Polychromatic418967fa.accept_13_12_7_11_1_1935 77 176 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 176 284 4 19 44 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 176 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 176 284 2 37 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 176 284 (accept_3_2 73 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 176 284 4 18 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 176 284 (Polychromatic418967fa.accept_23_2_15_8_1_17416 71 176 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 176 284 2 35 88 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 176 284
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 69 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 176 284 4 17 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 176 284 (accept_3_2 67 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 176 284 2 33 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 176 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 176 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 176 284 4 16 44 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 176 284
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 176 284 2 31 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 176 284 (accept_3_2 61 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 176 284 4 15 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 176 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 176 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 176 284 2 29 88 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 176 284
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 57 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 176 284 4 14 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 176 284 (accept_3_2 55 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 176 284 2 27 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 176 284 (Polychromatic418967fa.accept_13_1_7_11_1_702 53 176 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 284 4 13 44 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 284
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 51 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 176 284 2 25 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 176 284 (accept_3_2 49 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 284 4 12 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 176 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 284 2 23 88 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 284 4 11 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 284 (accept_3_2 43 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 284 2 21 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 284 (Polychromatic418967fa.accept_21_20_8_11_1_5407 41 176 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 284 4 10 44 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 284
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 284 2 19 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 284 (accept_3_2 37 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 284 4 9 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 176 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 176 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 284 2 17 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33
  176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 284 4 8 44 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 284 (accept_3_2 31
  176 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 284 2 15 88 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 284
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 29 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 176 284 4 7 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 176 284 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 176 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 284 2 13 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 284 (accept_3_2 25 176 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 284 4 6 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 284 (Polychromatic418967fa.accept_19_4_5_18_1_6647 23 176
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 284 2 11 88 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 284
  (Polychromatic418967fa.accept_19_2_5_18_1_10863 21 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 176 284 4 5 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 176 284 (accept_3_2 19 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 176 284 2 9 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 176 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 176 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 284 4 4 44 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 284 2 7 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 284 (accept_3_2 13 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 284 4 3 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 176 284 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 176 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 284 2 5 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 284 (Polychromatic418967fa.accept_13_9_7_11_1_1292
  9 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 284 4 2 44 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 284 (accept_3_2 7
  176 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 284 2 3 88 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 176 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 176 284 4 1 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 176 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 176 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 284 2 1 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 284 (accept_3_2 1 176 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 175 284 (Eq.refl Bool.true) (allA_of_3_0 110 175 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 174 284 (Eq.refl Bool.true) (allA_succ_of_gcd 110 174 284 2 55 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 174 284 (accept_3_2 109 174 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 174 284 2 54 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 174 284 (Polychromatic418967fa.accept_7_2_6_4_1_29
  107 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 174 284 2 53 87 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 174 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 105 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 174 284 2 52 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 174 284 (accept_3_2 103 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 174 284 2 51 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 174 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 101 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 174 284 2 50 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 174 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 99 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 174 284 2 49 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 174 284 (accept_3_2 97 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 174 284 2 48 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 174 284 (Polychromatic418967fa.accept_15_5_9_14_1_1724 95 174 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 174 284 2 47 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 174 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 93 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 174 284 2 46 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 174 284 (accept_3_2 91 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 174 284 2 45 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 174 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 89 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 174 284 2 44 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 174 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 87 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 174 284 2 43 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 174 284 (accept_3_2 85 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 174 284 2 42 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 174 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 174 284 2 41 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 174 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 174 284 2 40 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 174 284 (accept_3_2 79 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 174 284 2 39 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 174 284 (Polychromatic418967fa.accept_17_9_4_12_1_2958 77 174 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 174 284 2 38 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 174 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 174 284 2 37 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 174 284 (accept_3_2 73 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 284 2 36 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 174 284 2 35 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 174 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 174 284 2 34 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 174 284 (accept_3_2 67 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 284 2 33 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 174 284 2 32 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 174 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 174 284 2 31 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 174 284 (accept_3_2 61 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 284 2 30 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 284 2 29 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 174 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 174 284 2 28 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 174 284 (accept_3_2 55 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 284 2 27 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 284 2 26 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 174 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 174 284 2 25 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 174 284 (accept_3_2 49 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 284 2 24 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 284 2 23 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 174 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 174 284 2 22 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 174 284 (accept_3_2 43 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 284 2 21 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 284 (Polychromatic418967fa.accept_17_7_4_12_1_4084 41 174 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 284 2 20 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 174 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 174 284 2 19 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 174 284 (accept_3_2 37 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 284 2 18 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 284 2 17 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 174 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 174 284 2 16 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 174 284 (accept_3_2 31 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 284 2 15 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 284 2 14 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 284 2 13 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 284 (accept_3_2 25 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 284 2 12 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 284 2 11 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 284 2 10 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 284 (accept_3_2 19 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 284 2 9 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 284 2 8 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 284 2 7 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 284 (accept_3_2 13 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 284 2 6 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 174 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 284 2 5 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 284 2 4 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 284 (accept_3_2 7 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  284 2 3 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 174 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 284 2 2 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 174 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 284 2 1 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 284 (accept_3_2 1 174 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 173 284 (Eq.refl Bool.true) (allA_succ_of_accept 111 173 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 111 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 173 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 110 173 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 173 284 (accept_3_2 109 173 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 173 284 (Polychromatic418967fa.accept_24_12_5_20_1_14152 108 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 173 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 107 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 173 284 (accept_3_2 106 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 173 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 104 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 173 284 (accept_3_2 103 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 173 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 173
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 173 284
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 101 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 173 284 (accept_3_2 100 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 173 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 173 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 173 284 (accept_3_2 97 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 173 284 (Polychromatic418967fa.accept_9_6_2_5_1_506
  96 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 173 284
  (Polychromatic418967fa.accept_15_5_8_14_1_432 95 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 173 284 (accept_3_2 94 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 173 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 92 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 173 284 (accept_3_2 91 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 173 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 173 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 89 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 173 284 (accept_3_2 88 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 173 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 173 284 (accept_3_2 85 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 173 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 173 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 173 284 (accept_3_2 82 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 173 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 173 284 (accept_3_2 79 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 173 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 173 284
  (Polychromatic418967fa.accept_10_7_3_4_1_978 77 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 173 284 (accept_3_2 76 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 173 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 173 284 (accept_3_2 73 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 173 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 173 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 173 284 (accept_3_2 70 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 173 284 (Polychromatic418967fa.accept_16_4_13_12_1_1740 68 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 173 284 (accept_3_2 67 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 173 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 173 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 173 284 (accept_3_2 64 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 173 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 173 284 (accept_3_2 61 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 173 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 173 284
  (Polychromatic418967fa.accept_10_9_3_4_1_985 59 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 173 284 (accept_3_2 58 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 173 284 (Polychromatic418967fa.accept_16_8_13_12_1_3809 56 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 173 284 (accept_3_2 55 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 173 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 173
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 173 284 (accept_3_2 52 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 173 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 284 (accept_3_2 49 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 284
  (Polychromatic418967fa.accept_10_7_3_4_1_978 47 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 284 (accept_3_2 46 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 173 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 284 (accept_3_2 43 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 284 (accept_3_2 40 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 284 (accept_3_2 37 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 284 (accept_3_2 34 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 32 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 284 (accept_3_2 31 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 284 (accept_3_2 28 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 284 (accept_3_2 25 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 284 (accept_3_2 22 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 284 (accept_3_2 19 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 284 (Polychromatic418967fa.accept_21_18_5_11_1_7013 18 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 284 (accept_3_2 16 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 284 (accept_3_2 13 173 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 284
  (Polychromatic418967fa.accept_20_11_13_4_1_7573 11 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 173 284 (accept_3_2 10 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 284 (accept_3_2 7 173 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 284
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 284 (accept_3_2 4 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 173 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 284 (accept_3_2 1 173 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 172 284 (Eq.refl Bool.true) (allA_of_3_0 113 172 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 171 284 (Eq.refl Bool.true) (allA_succ_of_accept 113 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 171 284 (accept_3_2 112 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 171 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 111 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 171 284 (Polychromatic418967fa.accept_15_5_6_14_1_1721 110 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 171 284 (accept_3_2 109 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 171 284 (Polychromatic418967fa.accept_13_4_2_11_1_733 108 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 171 284 (accept_3_2 106 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 171 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 105 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 171 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 104 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 171 284 (accept_3_2 103 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 171 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 102 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 171 284 (accept_3_2 100 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 171 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 171 284 (Polychromatic418967fa.accept_15_8_6_14_1_975 98 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 171 284 (accept_3_2 97 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 171 284 (Polychromatic418967fa.accept_18_6_9_14_1_9915 96 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 171 284 (accept_3_2 94 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 171 284 (Polychromatic418967fa.accept_18_3_9_14_1_2219 93 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 171 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 92 171 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 171 284 (accept_3_2 91 171 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 171 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 171 284 (accept_3_2 88 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 171 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 171 284 (Polychromatic418967fa.accept_25_11_21_9_1_12308 86 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 171 284 (accept_3_2 85 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 171 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627 84 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 171 284 (accept_3_2 82 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 171 284 (Polychromatic418967fa.accept_13_3_2_11_1_1999 81 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 171 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 80 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 171 284 (accept_3_2 79 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 171 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 171 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 171 284 (accept_3_2 76 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 171 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 75 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 171 284 (Polychromatic418967fa.accept_13_9_2_11_1_1964 74 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 171 284 (accept_3_2 73 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 171 284 (Polychromatic418967fa.accept_16_8_11_12_1_962 72 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 171 284 (accept_3_2 70 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 171 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 171 284 (Polychromatic418967fa.accept_13_3_2_11_1_1999 68 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 284 (accept_3_2 67 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 171 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 171 284 (accept_3_2 64 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 171 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 171 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 171 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 284 (accept_3_2 61 171 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 171 284 (Polychromatic418967fa.accept_18_6_9_14_1_9915 60 171 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 284 (accept_3_2 58 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 171 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 171 284 (Polychromatic418967fa.accept_13_4_2_11_1_733 56 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 284 (accept_3_2 55 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 284 (accept_3_2 52 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 171 284 (Polychromatic418967fa.accept_27_24_9_14_1_17415 51 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 284 (accept_3_2 49 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 171 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 284 (accept_3_2 46 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 284 (Polychromatic418967fa.accept_23_21_10_8_1_9476 44 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 284 (accept_3_2 43 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 284 (accept_3_2 40 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 284 (Polychromatic418967fa.accept_15_8_6_14_1_975 38 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 284 (accept_3_2 37 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 171 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 284 (accept_3_2 34 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 284 (Polychromatic418967fa.accept_16_1_11_12_1_1774 33 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 284 (Polychromatic418967fa.accept_17_15_1_12_1_7910 32 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 284 (accept_3_2 31 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 284 (accept_3_2 28 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 284 (Polychromatic418967fa.accept_16_10_11_12_1_4835 26 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 284 (accept_3_2 25 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 171
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 284 (accept_3_2 22 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 284 (Polychromatic418967fa.accept_14_7_3_4_1_1816 21 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 171 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 284 (accept_3_2 19 171 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 284 (accept_3_2 16 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 284 (accept_3_2 13 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 284 (Polychromatic418967fa.accept_21_12_3_11_1_10078 12
  171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 284 (accept_3_2 10 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 284 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 171 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 284 (accept_3_2 7 171 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 284 (accept_3_2 4 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 171 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 284 (Polychromatic418967fa.accept_23_2_10_8_1_17414 2 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 284 (accept_3_2 1 171 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 170 284 (Eq.refl Bool.true) (allA_succ_of_gcd 114 170 284 2 57 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 170 284
  (Polychromatic418967fa.accept_12_5_2_8_1_172 113 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 170 284 2 56 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 170 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 111 170 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 170 284 2 55 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 170 284 (accept_3_2 109 170 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 170 284 2 54 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 170 284
  (Polychromatic418967fa.accept_12_11_2_8_1_511 107 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 170 284 2 53 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 170 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 105 170 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 170 284 2 52 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 170 284 (accept_3_2 103 170 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 170 284 2 51 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 170 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 101 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 170 284 2 50 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 170 284 (Polychromatic418967fa.accept_13_8_1_11_1_1284 99 170 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 170 284 2 49 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 170 284 (accept_3_2 97 170 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 170 284 2 48 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 170 284
  (Polychromatic418967fa.accept_11_7_5_9_1_884 95 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 170 284 2 47 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 170 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 93 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 170 284 2 46 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 170 284 (accept_3_2 91 170 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 170 284 2 45 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 170 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 89
  170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 170 284 2 44 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 170 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 87 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 170 284 2 43 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 170 284 (accept_3_2 85 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 170 284 2 42 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 170 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 170 284 2 41 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 170 284
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 81 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 170 284 2 40 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 170 284 (accept_3_2 79 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 170 284 2 39 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 170 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 170 284 2 38 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 170 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 170 284 2 37 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 170 284 (accept_3_2 73 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 170 284 2 36 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 170 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 170 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 170 284 2 35 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 170 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 170 284 2 34 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 170 284 (accept_3_2 67 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 170 284 2 33 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 170 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 170 284 2 32 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 284
  (Polychromatic418967fa.accept_23_17_9_8_1_17413 63 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 170 284 2 31 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 170 284 (accept_3_2 61 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 284 2 30 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 170 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 284 2 29 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 284 2 28 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 170 284 (accept_3_2 55 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 170 284 2 27 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 170 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 284 2 26 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 284 2 25 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 284 (accept_3_2 49 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 284 2 24 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 284 2 23 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 284
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 45 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 170 284 2 22 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 170 284 (accept_3_2 43 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 284 2 21 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 284 2 20 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 284 2 19 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 284 (accept_3_2 37 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 284 2 18 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 170 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 284 2 17 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 284 2 16 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 284 (accept_3_2 31 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 284 2 15 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 284 2 14 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 284 2 13 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 284 (accept_3_2 25 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 284 2 12 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 170 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 284 2 11 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 284 2 10 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 284 (accept_3_2 19 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 284 2 9 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 284 2 8 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 284 2 7 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 284 (accept_3_2 13 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 284 2 6 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 170 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 284 2 5 85 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 284
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 284 2 4 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 284 (accept_3_2 7 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  284 2 3 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 170 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 284 2 2 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 170 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 284 2 1 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 284 (accept_3_2 1 170 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 169 284 (Eq.refl Bool.true) (allA_of_3_0 116 169 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 117 168 284 (Eq.refl Bool.true) (allA_succ_of_gcd 116 168 284 4 29 42 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 168 284 (accept_3_2 115 168 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 168 284 2 57 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 168 284 (Polychromatic418967fa.accept_16_1_8_12_1_405
  113 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 168 284 4 28 42 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 168 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 111 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 168 284 2 55 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 168 284 (accept_3_2 109 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 168 284 4 27 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 168 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 107 168 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 168 284 2 53 84 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 168 284
  (Polychromatic418967fa.accept_11_6_3_9_1_906 105 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 168 284 4 26 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 168 284 (accept_3_2 103 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 168 284 2 51 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 168 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 101 168 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 168 284 4 25 42 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 168 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 99 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 168 284 2 49 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 168 284 (accept_3_2 97 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 168 284 4 24 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 168 284 (Polychromatic418967fa.accept_13_4_12_11_1_5362 95 168 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 168 284 2 47 84 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 168 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 93 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 168 284 4 23 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 168 284 (accept_3_2 91 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 168 284 2 45 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 168 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 89 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 168 284 4 22 42 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 168 284
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 87 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 168 284 2 43 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 168 284 (accept_3_2 85 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 168 284 4 21 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 168 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 168 284 2 41 84 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 168 284
  (Polychromatic418967fa.accept_16_1_8_12_1_405 81 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 168 284 4 20 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 168 284 (accept_3_2 79 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 168 284 2 39 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 168 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 77 168 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 168 284 4 19 42 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 168 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 168 284 2 37 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 168 284 (accept_3_2 73 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 168 284 4 18 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 168 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 284 2 35 84 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 168 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 69 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 168 284 4 17 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 168 284 (accept_3_2 67 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 284 2 33 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 284 4 16 42 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 168 284
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 168 284 2 31 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 168 284 (accept_3_2 61 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 284 4 15 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 284 2 29 84 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 168 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 168 284 4 14 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 168 284 (accept_3_2 55 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 284 2 27 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 284 4 13 42 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 168 284
  (Polychromatic418967fa.accept_16_3_8_12_1_2736 51 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 168 284 2 25 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 168 284 (accept_3_2 49 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 284 4 12 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 284 2 23 84 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 168 284
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 168 284 4 11 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 168 284 (accept_3_2 43 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 284 2 21 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 284 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 168 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 284 4 10 42 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 168 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 168 284 2 19 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 168 284 (accept_3_2 37 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 284 4 9 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 168 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 168 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 284 2 17 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 284
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 168 284 4 8 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 168 284 (accept_3_2 31 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 284 2 15 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 284 4 7 42 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 284
  (Polychromatic418967fa.accept_13_1_12_11_1_728 27 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 168 284 2 13 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 168 284 (accept_3_2 25 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 284 4 6 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 284 (Polychromatic418967fa.accept_13_10_12_11_1_731 23 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 284 2 11 84 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 284 4 5 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 168 284 (accept_3_2 19 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  168 284 2 9 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 168 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 284 4 4 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 284
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 284 2 7 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 284 (accept_3_2 13 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 284 4 3 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 168 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 168 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 284 2 5 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 9
  168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 284 4 2 42 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 284 (accept_3_2 7
  168 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 284 2 3 84 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 284
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 5 168 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 168 284 4 1 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 168 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 168 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 284 2 1 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 284 (accept_3_2 1 168 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 168
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 167 284 (Eq.refl Bool.true) (allA_succ_of_accept 117 167 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 117 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 167 284 (Polychromatic418967fa.accept_16_4_7_12_1_2734 116 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 167 284 (accept_3_2 115 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 167 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 114 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 167 284
  (Polychromatic418967fa.accept_10_3_7_4_1_584 113 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 167 284 (accept_3_2 112 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 167 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 110 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 167 284 (accept_3_2 109 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 167 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 167
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 167 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 107 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 167 284 (accept_3_2 106 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 167 284 (Polychromatic418967fa.accept_16_8_7_12_1_7207 104 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 167 284 (accept_3_2 103 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 167 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 102 167
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 167 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 101 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 167 284 (accept_3_2 100 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 167 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 98 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 167 284 (accept_3_2 97 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 167 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 167 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 167 284
  (Polychromatic418967fa.accept_11_7_2_9_1_480 95 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 167 284 (accept_3_2 94 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 167 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 92 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 167 284 (accept_3_2 91 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 167 284 (Polychromatic418967fa.accept_19_14_15_18_1_5250 90
  167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 167 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 89 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 167 284 (accept_3_2 88 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 167 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 167 284 (accept_3_2 85 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 167 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 84 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 167 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 83 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 167 284 (accept_3_2 82 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 167 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 167 284 (accept_3_2 79 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 167 284 (Polychromatic418967fa.accept_15_3_2_14_1_1713 78 167 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 167 284
  (Polychromatic418967fa.accept_17_9_14_12_1_9177 77 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 167 284 (accept_3_2 76 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 167 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 167 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 167
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 167 284 (accept_3_2 73 167
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 167 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 167 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 71 167 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 167 284 (accept_3_2 70 167 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 167 284 (Polychromatic418967fa.accept_7_5_6_4_1_117
  68 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 284 (accept_3_2 67
  167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 167 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 167 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 167 284 (accept_3_2 64 167 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 284 (Polychromatic418967fa.accept_10_2_7_4_1_967
  62 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 284 (accept_3_2 61
  167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 284
  (Polychromatic418967fa.accept_17_9_14_12_1_9177 60 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 167 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 284 (accept_3_2 58 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 284
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 56 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 284 (accept_3_2 55 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 167 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 53 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 284 (accept_3_2 52 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 167 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 167 284 (accept_3_2 49 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 167 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 167 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 284 (accept_3_2 46 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 284 (accept_3_2 43 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 41 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 284 (accept_3_2 40 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 284 (accept_3_2 37 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 284 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 284 (accept_3_2 34 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 284 (accept_3_2 31 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 284 (accept_3_2 28 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 284 (accept_3_2 25 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 284 (accept_3_2 22 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 284
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 284 (accept_3_2 19 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 284 (accept_3_2 16 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 284 (accept_3_2 13 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 284 (accept_3_2 10 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 284
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 284 (accept_3_2 7 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 284 (Polychromatic418967fa.accept_21_6_20_11_1_7067 6 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 284 (accept_3_2 4 167 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 284 (accept_3_2 1 167 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 166 284 (Eq.refl Bool.true) (allA_of_3_0 119 166 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 120 165 284 (Eq.refl Bool.true) (allA_succ_of_accept 119 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 165 284 (accept_3_2 118 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 165 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 117 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 116 165 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 116 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 165 284 (accept_3_2 115 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 114 165
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 165 284 (accept_3_2 112 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 165 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 111 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 165 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 110 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 165 284 (accept_3_2 109 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 165 284 (Polychromatic418967fa.accept_21_3_18_11_1_10061 108
  165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 165 284 (accept_3_2 106 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 165 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 105 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 165 284 (Polychromatic418967fa.accept_16_8_5_12_1_3812 104 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 165 284 (accept_3_2 103 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 165 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 102 165
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 165 284 (accept_3_2 100 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 165 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 99 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 165 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 165 284 (accept_3_2 97 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 165 284 (accept_3_2 94 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 165 284 (Polychromatic418967fa.accept_13_2_9_11_1_258 93 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 165 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 92 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 165 284 (accept_3_2 91 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 165 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 165 284 (accept_3_2 88 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 165 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 86 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 165 284 (accept_3_2 85 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 165 284 (Polychromatic418967fa.accept_16_4_5_12_1_2749 84 165
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 165 284 (accept_3_2 82 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 165 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 165 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 165 284 (accept_3_2 79 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 165 284 (accept_3_2 76 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 165 284 (Polychromatic418967fa.accept_20_15_5_4_1_4566 75 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 165 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 284 (accept_3_2 73 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 165 284 (Polychromatic418967fa.accept_13_7_9_11_1_705 72 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 165 284 (accept_3_2 70 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 165 284 (Polychromatic418967fa.accept_16_4_5_12_1_2749 68 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 284 (accept_3_2 67 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 165
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 284 (accept_3_2 64 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 165 284 (Polychromatic418967fa.accept_14_7_11_4_1_3455 63 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 165 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 284 (accept_3_2 61 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 284 (accept_3_2 58 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 165 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 165 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 284 (accept_3_2 55 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 284 (accept_3_2 52 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 165 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 50 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 284 (accept_3_2 49 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 284 (Polychromatic418967fa.accept_18_12_3_14_1_5919 48 165
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 284 (accept_3_2 46 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 165 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 45 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 165 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 284 (accept_3_2 43 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 284 (accept_3_2 40 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 165 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 284 (accept_3_2 37 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 165 284 (accept_3_2 34 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 165 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 165 284 (Polychromatic418967fa.accept_23_9_4_8_1_17412 32 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 284 (accept_3_2 31 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 165
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 284 (accept_3_2 28 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 284 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 284 (accept_3_2 25 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 284 (accept_3_2 22 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 165 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 284 (accept_3_2 19 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 284 (accept_3_2 16 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 284 (Polychromatic418967fa.accept_13_1_9_11_1_703 14 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 284 (accept_3_2 13 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 284 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 165
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 284 (accept_3_2 10 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  165 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 284 (accept_3_2 7 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 165 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 284 (accept_3_2 4 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 284 (Polychromatic418967fa.accept_21_3_18_11_1_10061 3 165 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 284 (accept_3_2 1 165 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 164 284 (Eq.refl Bool.true) (allA_succ_of_gcd 120 164 284 4 30 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 164 284
  (Polychromatic418967fa.accept_14_7_10_4_1_130 119 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 164 284 2 59 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 164 284 (Polychromatic418967fa.accept_16_5_4_12_1_3800 117 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 164 284 4 29 41 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 164 284 (accept_3_2 115 164 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 164 284 2 57 82 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 164 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 113 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 164 284 4 28 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 164 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 111 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 164 284 2 55 82 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 164 284 (accept_3_2 109 164 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 164 284 4 27 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 164 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 107 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 164 284 2 53 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 164 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 105 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 164 284 4 26 41 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 164 284 (accept_3_2 103 164 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 164 284 2 51 82 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 164 284
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 101 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 164 284 4 25 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 164 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 164 284 2 49 82 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 164 284 (accept_3_2 97 164 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 164 284 4 24 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 164 284
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 95 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 164 284 2 47 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 164 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 93 164 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 164 284 4 23 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 164 284 (accept_3_2 91 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 164 284 2 45 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 164 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 89
  164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 164 284 4 22 41 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 164 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 87 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 164 284 2 43 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 164 284 (accept_3_2 85 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 164 284 4 21 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 164 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 164 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 164 284 2 41 82 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 164 284
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 81 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 164 284 4 20 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 164 284 (accept_3_2 79 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 164 284 2 39 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 164 284 (Polychromatic418967fa.accept_14_7_10_4_1_130 77 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 164 284 4 19 41 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 164 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 75 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 164 284 2 37 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 164 284 (accept_3_2 73 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 164 284 4 18 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 164 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 164 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 284 2 35 82 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 284 4 17 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 284 (accept_3_2 67 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 284 2 33 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 284 (Polychromatic418967fa.accept_16_1_4_12_1_376 65 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 284 4 16 41 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 284
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 164 284 2 31 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 164 284 (accept_3_2 61 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 284 4 15 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 284 (Polychromatic418967fa.accept_16_11_4_12_1_1760 59 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 284 2 29 82 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 284 4 14 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 284 (accept_3_2 55 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 284 2 27 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 164 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 284 4 13 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 284 2 25 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 284 (accept_3_2 49 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 284 4 12 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 284 (Polychromatic418967fa.accept_16_15_4_12_1_2731 47 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 284 2 23 82 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 284
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 284 4 11 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 284 (accept_3_2 43 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 284 2 21 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 164 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 284 4 10 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 284 2 19 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 284 (accept_3_2 37 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 284 4 9 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 164 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 284 2 17 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 33
  164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 284 4 8 41 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 284 (accept_3_2 31
  164 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 284 2 15 82 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 164 284 4 7 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 164 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 164 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 284 2 13 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 284 (accept_3_2 25 164 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 284 4 6 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 164
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 284 2 11 82 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 284 4 5 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 164 284 (accept_3_2 19 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  164 284 2 9 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 164 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 164 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 284 4 4 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 284 2 7 82 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 284 (accept_3_2 13
  164 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 284 4 3 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 284
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 164 284 2 5 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 164 284 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 284 4 2 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 284 (accept_3_2 7 164 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 284 2 3 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 284 (Polychromatic418967fa.accept_16_5_4_12_1_3800
  5 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 284 4 1 41 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 164 284 2 1 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 164 284 (accept_3_2 1 164 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 163 284 (Eq.refl Bool.true) (allA_of_3_0 122 163 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 123 162 284 (Eq.refl Bool.true) (allA_succ_of_gcd 122 162 284 2 61 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 162 284 (accept_3_2 121 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 162 284 2 60 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 162 284
  (Polychromatic418967fa.accept_16_7_2_12_1_1754 119 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 162 284 2 59 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 117 162 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 117 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 162 284 2 58 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 162 284 (accept_3_2 115 162 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 162 284 2 57 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 162 284
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 113 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 162 284 2 56 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 111 162 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 111 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 162 284 2 55 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 162 284 (accept_3_2 109 162 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 162 284 2 54 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 162 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 107 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 162 284 2 53 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 162 284 (Polychromatic418967fa.accept_12_9_6_8_1_518 105 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 162 284 2 52 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 162 284 (accept_3_2 103 162 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 162 284 2 51 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 162 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 101 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 162 284 2 50 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 162 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 162 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 162 284 2 49 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 162 284 (accept_3_2 97 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 162 284 2 48 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 162 284 (Polychromatic418967fa.accept_13_4_6_11_1_2017
  95 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 162 284 2 47 81 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 162 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 93 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 162 284 2 46 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 162 284 (accept_3_2 91 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 162 284 2 45 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 162 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 162 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 162 284 2 44 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 162 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 87 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 162 284 2 43 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 162 284 (accept_3_2 85 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 162 284 2 42 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 162 284 (Polychromatic418967fa.accept_13_5_6_11_1_1933 83 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 162 284 2 41 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 162 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 162 284 2 40 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 162 284 (accept_3_2 79 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 284 2 39 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 162 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 162 284 2 38 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 162 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 162 284 2 37 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 162 284 (accept_3_2 73 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 284 2 36 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 162 284 (Polychromatic418967fa.accept_15_11_12_14_1_2612 71 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 284 2 35 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 162 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 162 284 2 34 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 162 284 (accept_3_2 67 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 284 2 33 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 65 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 284 2 32 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 162 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 162 284 2 31 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 162 284 (accept_3_2 61 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 284 2 30 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 162 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 284 2 29 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 162 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 162 284 2 28 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 162 284 (accept_3_2 55 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 284 2 27 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 284 (Polychromatic418967fa.accept_14_11_8_4_1_2628 53 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 284 2 26 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 162 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 162 284 2 25 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 162 284 (accept_3_2 49 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 284 2 24 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 162 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 284 2 23 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 284 2 22 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 284 (accept_3_2 43 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 284 2 21 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 284 (Polychromatic418967fa.accept_15_11_12_14_1_2612 41 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 284 2 20 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 284 2 19 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 284 (accept_3_2 37 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 284 2 18 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 284 (Polychromatic418967fa.accept_20_15_2_4_1_11882 35 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 284 2 17 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 284 2 16 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 284 (accept_3_2 31 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 284 2 15 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 284 (Polychromatic418967fa.accept_20_9_2_4_1_9093 29 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 284 2 14 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 284 2 13 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 284 (accept_3_2 25 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 284 2 12 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 284 (Polychromatic418967fa.accept_16_7_2_12_1_1754 23 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 284 2 11 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 284
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 284 2 10 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 284 (accept_3_2 19 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 284 2 9 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 162 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 284 2 8 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 284 2 7 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 284 (accept_3_2 13 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 284 2 6 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 284 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 284 2 5 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 284 2 4 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 284 (accept_3_2 7 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  284 2 3 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 162 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 284 2 2 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 162 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 284 2 1 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 284 (accept_3_2 1 162 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 161 284 (Eq.refl Bool.true) (allA_succ_of_accept 123 161 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 123 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 161 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 122 161 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 161 284 (accept_3_2 121 161 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 161 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 120 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 161 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 119 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 161 284 (accept_3_2 118 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 161 284 (Polychromatic418967fa.accept_16_4_1_12_1_1792 116 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 161 284 (accept_3_2 115 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 161 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 114 161
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 161 284
  (Polychromatic418967fa.accept_21_8_14_11_1_11676 113 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 161 284 (accept_3_2 112 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 161 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 161 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 110 161
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 161 284 (accept_3_2 109 161
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 161 284
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 108 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 161 284 (Polychromatic418967fa.accept_10_7_1_4_1_1447 107 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 161 284 (accept_3_2 106 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 161
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 161 284
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 104 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 161 284 (accept_3_2 103 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 161 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 161 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 101 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 161 284 (accept_3_2 100 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 161 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 161 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 98 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 161 284 (accept_3_2 97 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 161 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 161 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 95 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 161 284 (accept_3_2 94 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 161 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 161 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 161 284 (accept_3_2 91 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 161 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 90 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 161 284 (Polychromatic418967fa.accept_17_4_8_12_1_9165 89 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 161 284 (accept_3_2 88 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 161 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 161 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 161 284 (accept_3_2 85 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 161 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 161 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 284 (accept_3_2 82 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 284
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 80 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 161 284 (accept_3_2 79 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 161 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 161 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 284 (accept_3_2 76 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 161 284 (accept_3_2 73 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 161 284 (Polychromatic418967fa.accept_13_7_5_11_1_1927 72 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 161 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 71 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 284 (accept_3_2 70 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 161 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 284
  (Polychromatic418967fa.accept_11_2_7_9_1_890 68 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 284 (accept_3_2 67 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 284 (accept_3_2 64 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 284 (accept_3_2 61 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 284 (Polychromatic418967fa.accept_13_7_5_11_1_1927 59 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 284 (accept_3_2 58 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 161 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 284 (accept_3_2 55 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 284 (Polychromatic418967fa.accept_17_3_8_12_1_6573 54 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 284 (accept_3_2 52 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 284 (accept_3_2 49 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 284 (accept_3_2 46 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 284
  (Polychromatic418967fa.accept_17_10_8_12_1_6559 44 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 161 284 (accept_3_2 43 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 161 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 161 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 284 (Polychromatic418967fa.accept_19_3_9_18_1_10979 41 161
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 284 (accept_3_2 40 161
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 161 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 161 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 284 (accept_3_2 37 161 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 161 284 (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 284
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 161 284 (accept_3_2 34 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 284 (Polychromatic418967fa.accept_13_6_5_11_1_1971 32 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 284 (accept_3_2 31 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 161 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 284
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 284 (accept_3_2 28 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 284 (accept_3_2 25 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 161 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 284
  (Polychromatic418967fa.accept_20_3_1_4_1_7654 23 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 284 (accept_3_2 22 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 161 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 284 (accept_3_2 19 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 284 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 161 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 284
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 284 (accept_3_2 16 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 284 (accept_3_2 13 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 161 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 284 (accept_3_2 10 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 284 (Polychromatic418967fa.accept_16_8_1_12_1_984 8 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 284 (accept_3_2 7 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 161 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 284
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 284 (accept_3_2 4 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 161 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 284 (accept_3_2 1 161 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 160 284 (Eq.refl Bool.true) (allA_of_3_0 125 160 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 126 159 284 (Eq.refl Bool.true) (allA_succ_of_accept 125 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 159 284 (accept_3_2 124 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 159 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 123 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 159 284 (Polychromatic418967fa.accept_13_5_3_11_1_1288 122 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 159 284 (accept_3_2 121 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 159 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 120 159
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 159 284 (accept_3_2 118 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 159 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 117 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 159 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 116 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 159 284 (accept_3_2 115 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 159 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 114 159
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 159 284 (accept_3_2 112 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 159 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 111 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 159 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 110 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 159 284 (accept_3_2 109 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 159 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 108 159
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 159 284 (accept_3_2 106 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 159 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 105 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 159 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 104 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 159 284 (accept_3_2 103 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 159 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 159
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 159 284 (accept_3_2 100 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 159 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 99 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 159 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 159 284 (accept_3_2 97 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 159 284 (Polychromatic418967fa.accept_13_5_3_11_1_1288 96 159 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 159 284 (accept_3_2 94 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 159 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 159 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 92 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 284 (accept_3_2 91 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 159 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 159 284 (accept_3_2 88 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 159 284 (Polychromatic418967fa.accept_15_12_9_14_1_2635 87 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 159 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 284 (accept_3_2 85 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 159 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 159 284 (accept_3_2 82 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 159 284 (Polychromatic418967fa.accept_15_6_9_14_1_3457 81 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 159 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 284 (accept_3_2 79 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 159 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 159 284 (accept_3_2 76 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 159 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 159 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 284 (accept_3_2 73 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 159 284 (accept_3_2 70 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 159 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 159 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 68 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 284 (accept_3_2 67 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 159 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 159 284 (accept_3_2 64 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 159 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 159 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 284 (accept_3_2 61 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 284 (Polychromatic418967fa.accept_13_8_3_11_1_3467 60 159 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 159 284 (accept_3_2 58 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 159 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 159 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 284 (accept_3_2 55 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 284 (accept_3_2 52 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 159 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 159 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 284 (accept_3_2 49 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 284 (accept_3_2 46 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 159 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 159 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 284 (accept_3_2 43 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 284 (accept_3_2 40 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 284 (accept_3_2 37 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 284 (accept_3_2 34 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 284 (Polychromatic418967fa.accept_24_8_15_20_1_17411 32 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 284 (accept_3_2 31 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 159 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 284 (accept_3_2 28 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 284 (accept_3_2 25 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 284 (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 159 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 284 (accept_3_2 22 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 284 (accept_3_2 19 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 284 (accept_3_2 16 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 284 (Polychromatic418967fa.accept_13_1_3_11_1_1289 14 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 284 (accept_3_2 13 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 159 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 284 (accept_3_2 10 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 284 (accept_3_2 7 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 159 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 284 (accept_3_2 4 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 159 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 284 (accept_3_2 1 159 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 158 284 (Eq.refl Bool.true) (allA_succ_of_gcd 126 158 284 2 63 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 158 284
  (Polychromatic418967fa.accept_12_5_2_8_1_172 125 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 158 284 2 62 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 158 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 123 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 158 284 2 61 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 158 284 (accept_3_2 121 158 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 158 284 2 60 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 158 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 119 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 158 284 2 59 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 158 284 (Polychromatic418967fa.accept_19_3_6_18_1_2665 117 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 158 284 2 58 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 158 284 (accept_3_2 115 158 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 158 284 2 57 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 158 284
  (Polychromatic418967fa.accept_12_5_2_8_1_172 113 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 158 284 2 56 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 158 284 (Polychromatic418967fa.accept_15_6_8_14_1_4575 111 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 158 284 2 55 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 158 284 (accept_3_2 109 158 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 158 284 2 54 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 158 284
  (Polychromatic418967fa.accept_12_11_2_8_1_511 107 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 158 284 2 53 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 158 284 (Polychromatic418967fa.accept_22_17_4_20_1_8173 105 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 158 284 2 52 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 158 284 (accept_3_2 103 158 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 158 284 2 51 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 158 284
  (Polychromatic418967fa.accept_11_2_4_9_1_484 101 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 158 284 2 50 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 158 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 99 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 158 284 2 49 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 158 284 (accept_3_2 97 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 158 284 2 48 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 158 284 (Polychromatic418967fa.accept_12_11_2_8_1_511
  95 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 158 284 2 47 79 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 158 284
  (Polychromatic418967fa.accept_17_8_5_12_1_7925 93 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 158 284 2 46 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 158 284 (accept_3_2 91 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 158 284 2 45 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 158 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 89 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 158 284 2 44 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 158 284
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 87 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 158 284 2 43 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 158 284 (accept_3_2 85 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 158 284 2 42 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 158 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 158 284 2 41 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 284
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 81 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 158 284 2 40 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 158 284 (accept_3_2 79 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 158 284 2 39 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 158 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 284 2 38 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 284
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 75 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 158 284 2 37 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 158 284 (accept_3_2 73 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 284 2 36 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 284 2 35 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 69 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 284 2 34 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 284 (accept_3_2 67 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 284 2 33 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 284 2 32 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 284
  (Polychromatic418967fa.accept_27_9_23_14_1_2233 63 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 158 284 2 31 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 158 284 (accept_3_2 61 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 284 2 30 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 284 2 29 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 284
  (Polychromatic418967fa.accept_11_2_4_9_1_484 57 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 284 2 28 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 284 (accept_3_2 55 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 284 2 27 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 284 2 26 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 284
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 51 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 284 2 25 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 284 (accept_3_2 49 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 284 2 24 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 284 2 23 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 284
  (Polychromatic418967fa.accept_19_7_6_18_1_8123 45 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 284 2 22 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 284 (accept_3_2 43 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 284 2 21 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 284 2 20 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 284 2 19 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 284 (accept_3_2 37 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 284 2 18 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 284 2 17 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 284
  (Polychromatic418967fa.accept_26_7_2_24_1_17410 33 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 158 284 2 16 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 158 284 (accept_3_2 31 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 284 2 15 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 284 2 14 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 284
  (Polychromatic418967fa.accept_17_10_5_12_1_4101 27 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 158 284 2 13 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 158 284 (accept_3_2 25 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 284 2 12 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 284 2 11 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 284
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 284 2 10 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 284 (accept_3_2 19 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 284 2 9 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 158 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 284 2 8 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 284
  (Polychromatic418967fa.accept_22_15_4_20_1_9799 15 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 158 284 2 7 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 158 284 (accept_3_2 13 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 284 2 6 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 284 2 5 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 284 2 4 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 284 (accept_3_2 7 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  284 2 3 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 158 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 284 2 2 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 284 (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 158 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 284 2 1 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 284 (accept_3_2 1 158 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 157 284 (Eq.refl Bool.true) (allA_of_3_0 128 157 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 129 156 284 (Eq.refl Bool.true) (allA_succ_of_gcd 128 156 284 4 32 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 156 284 (accept_3_2 127 156 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 156 284 2 63 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 156 284 (Polychromatic418967fa.accept_7_6_2_4_1_291
  125 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 156 284 4 31 39 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 156 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 123 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 156 284 2 61 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 156 284 (accept_3_2 121 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 156 284 4 30 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 156 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 119 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 156 284 2 59 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 156 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 117 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 156 284 4 29 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 156 284 (accept_3_2 115 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 156 284 2 57 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 156 284 (Polychromatic418967fa.accept_15_8_6_14_1_975 113 156 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 156 284 4 28 39 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 156 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 111 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 156 284 2 55 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 156 284 (accept_3_2 109 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 156 284 4 27 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 156 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 107 156 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 156 284 2 53 78 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 156 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 105 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 156 284 4 26 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 156 284 (accept_3_2 103 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 156 284 2 51 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 156 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 101 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 156 284 4 25 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 156 284
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 99 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 156 284 2 49 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 156 284 (accept_3_2 97 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 156 284 4 24 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 156 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 95 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 156 284 2 47 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 156 284
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 93 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 156 284 4 23 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 156 284 (accept_3_2 91 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 156 284 2 45 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 156 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 156 284 4 22 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 156 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 87 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 156 284 2 43 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 156 284 (accept_3_2 85 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 156 284 4 21 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 156 284 2 41 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 156 284
  (Polychromatic418967fa.accept_11_4_2_9_1_496 81 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 156 284 4 20 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 156 284 (accept_3_2 79 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 284 2 39 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 284 (Polychromatic418967fa.accept_22_11_2_20_1_904 77 156 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 156 284 4 19 39 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 156 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 156 284 2 37 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 156 284 (accept_3_2 73 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 284 4 18 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 284 2 35 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 156 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 156 284 4 17 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 156 284 (accept_3_2 67 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 284 2 33 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 284 4 16 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 284
  (Polychromatic418967fa.accept_22_19_2_20_1_14362 63 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 156 284 2 31 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 156 284 (accept_3_2 61 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 284 4 15 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 59 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 284 2 29 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 284
  (Polychromatic418967fa.accept_18_3_12_14_1_2232 57 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 156 284 4 14 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 156 284 (accept_3_2 55 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 284 2 27 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 284 4 13 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 284 2 25 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 284 (accept_3_2 49 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 284 4 12 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 284 2 23 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 284 4 11 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 284 (accept_3_2 43 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 284 2 21 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 284 4 10 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 284
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 284 2 19 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 284 (accept_3_2 37 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 284 4 9 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 156 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 284 2 17 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 284 4 8 39 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 284 (accept_3_2 31
  156 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 284 2 15 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 284 4 7 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 156 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 156 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 284 2 13 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 284 (accept_3_2 25 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 284 4 6 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 156
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 284 2 11 78 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 284
  (Polychromatic418967fa.accept_18_3_12_14_1_2232 21 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 156 284 4 5 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 156 284 (accept_3_2 19 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 284 2 9 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 284 4 4 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 156 284 2 7 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 156 284 (accept_3_2 13 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 284 4 3 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 156 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 156 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 284 2 5 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9
  156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 284 4 2 39 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 284 (accept_3_2 7
  156 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 284 2 3 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 156 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 156 284 4 1 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 156 284 (Polychromatic418967fa.accept_18_3_12_14_1_2232 3 156 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 284 2 1 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 284 (accept_3_2 1 156 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 156
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 130 155 284 (Eq.refl Bool.true) (allA_succ_of_accept 129 155 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 129 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 155 284 (Polychromatic418967fa.accept_15_8_5_14_1_986 128 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 155 284 (accept_3_2 127 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 126 155 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 126 155 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 155 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 125 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 155 284 (accept_3_2 124 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 155 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 122 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 155 284 (accept_3_2 121 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 155 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 120 155
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 155 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 119 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 155 284 (accept_3_2 118 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 155 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 116 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 155 284 (accept_3_2 115 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 155 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 114 155
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 155 284
  (Polychromatic418967fa.accept_15_8_5_14_1_986 113 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 155 284 (accept_3_2 112 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 155 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 110 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 155 284 (accept_3_2 109 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 155 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 108 155
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 155 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 107 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 155 284 (accept_3_2 106 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 155 284 (Polychromatic418967fa.accept_16_8_11_12_1_962 104 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 155 284 (accept_3_2 103 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 155 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 155
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 155 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 101 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 155 284 (accept_3_2 100 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 155 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 155 284 (accept_3_2 97 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 155 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 155 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 95 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 155 284 (accept_3_2 94 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 155 284 (Polychromatic418967fa.accept_13_1_12_11_1_728 92 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 155 284 (accept_3_2 91 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 155 284 (Polychromatic418967fa.accept_16_10_11_12_1_4835 90
  155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 155 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 89 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 155 284 (accept_3_2 88 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 155 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 86 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 155 284 (accept_3_2 85 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 155 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 155 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 155 284
  (Polychromatic418967fa.accept_15_8_5_14_1_986 83 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 155 284 (accept_3_2 82 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 155 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 80 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 155 284 (accept_3_2 79 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 155 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 284
  (Polychromatic418967fa.accept_15_2_5_14_1_61 77 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 155 284 (accept_3_2 76 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 155 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 284 (accept_3_2 73 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 155 284 (Polychromatic418967fa.accept_13_7_12_11_1_1911 72 155
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 155 284 (accept_3_2 70 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 155 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 284 (accept_3_2 67 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 155 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 284
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 65 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 284 (accept_3_2 64 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 284 (accept_3_2 61 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 284 (accept_3_2 58 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 284 (accept_3_2 55 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 155 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 284 (accept_3_2 52 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 284 (accept_3_2 49 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 155 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 284 (accept_3_2 46 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 284 (accept_3_2 43 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 284
  (Polychromatic418967fa.accept_10_1_5_4_1_276 41 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 284 (accept_3_2 40 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 284 (accept_3_2 37 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 284 (accept_3_2 34 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 284 (accept_3_2 31 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 155 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 284
  (Polychromatic418967fa.accept_10_9_5_4_1_966 29 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 284 (accept_3_2 28 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 284 (accept_3_2 25 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 284 (accept_3_2 22 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 284 (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 284 (accept_3_2 19 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 284 (Polychromatic418967fa.accept_21_18_8_11_1_10083 18
  155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 284 (accept_3_2 16 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 284 (accept_3_2 13 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 155 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 284
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 284 (accept_3_2 10 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 284 (accept_3_2 7 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 155 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 284 (accept_3_2 4 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 284 (accept_3_2 1 155 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 154 284 (Eq.refl Bool.true) (allA_of_3_0 131 154 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 132 153 284 (Eq.refl Bool.true) (allA_succ_of_accept 131 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 131 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 153 284 (accept_3_2 130 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 129 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 128 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 153 284 (accept_3_2 127 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 153 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 126 153
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 153 284 (accept_3_2 124 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 153 284 (Polychromatic418967fa.accept_20_3_13_4_1_17409 123 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 122 153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 122 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 153 284 (accept_3_2 121 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 153 284 (Polychromatic418967fa.accept_13_3_10_11_1_1293 120
  153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 153 284 (accept_3_2 118 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 153 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 117 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 153 284 (Polychromatic418967fa.accept_13_12_10_11_1_1279 116 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 153 284 (accept_3_2 115 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 114 153
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 153 284 (accept_3_2 112 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 153 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 111 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 153 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 110 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 153 284 (accept_3_2 109 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 153
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 153 284 (accept_3_2 106 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 153 284 (Polychromatic418967fa.accept_13_1_10_11_1_1280 105 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 153 284 (Polychromatic418967fa.accept_16_8_9_12_1_1737 104 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 153 284 (accept_3_2 103 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 153 284 (Polychromatic418967fa.accept_12_6_9_8_1_165
  102 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 153 284 (accept_3_2 100 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 153 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 99 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 153 284 (Polychromatic418967fa.accept_16_2_9_12_1_46 98 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 284 (accept_3_2 97 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 153 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 153 284 (accept_3_2 94 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 153 284 (Polychromatic418967fa.accept_13_1_10_11_1_1280 92 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 284 (accept_3_2 91 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 153 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 153
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 153 284 (accept_3_2 88 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 284 (accept_3_2 85 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 153 284 (Polychromatic418967fa.accept_16_4_9_12_1_4829 84 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 153 284 (accept_3_2 82 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 153 284 (Polychromatic418967fa.accept_13_3_10_11_1_1293 81 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 284 (accept_3_2 79 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 153 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 78 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 153 284 (accept_3_2 76 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 153 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 153 284 (Polychromatic418967fa.accept_11_8_10_9_1_1401 74 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 284 (accept_3_2 73 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 153 284 (accept_3_2 70 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 153 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 153 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 284 (accept_3_2 67 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 153 284 (accept_3_2 64 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 153 284 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 153 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 62 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 284 (accept_3_2 61 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 284 (Polychromatic418967fa.accept_13_8_10_11_1_2730 60 153
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 153 284 (accept_3_2 58 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 153 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 153 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 56 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 284 (accept_3_2 55 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 153 284 (accept_3_2 52 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 153 284 (Polychromatic418967fa.accept_16_2_9_12_1_46 50 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 284 (accept_3_2 49 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 284 (Polychromatic418967fa.accept_22_4_21_20_1_14455 48
  153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 284 (accept_3_2 46 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 284 (accept_3_2 43 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 284 (accept_3_2 40 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 284 (accept_3_2 37 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 284 (Polychromatic418967fa.accept_16_4_9_12_1_4829 36 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 284 (accept_3_2 34 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 153 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 32 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 284 (accept_3_2 31 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 284 (accept_3_2 28 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 284 (accept_3_2 25 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 284 (accept_3_2 22 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 284 (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 284 (accept_3_2 19 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 153
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 284 (accept_3_2 16 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 284 (Polychromatic418967fa.accept_13_2_10_11_1_1276 15 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 284 (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 284 (accept_3_2 13 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 284 (accept_3_2 10 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 284 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 284 (accept_3_2 7 153 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 153 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 284 (accept_3_2 4 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 153 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 284 (accept_3_2 1 153 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 133 152 284 (Eq.refl Bool.true) (allA_succ_of_gcd 132 152 284 4 33 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 152 284
  (Polychromatic418967fa.accept_13_1_9_11_1_703 131 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 152 284 2 65 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 152 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 129 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 152 284 4 32 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 152 284 (accept_3_2 127 152 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 152 284 2 63 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 152 284 (Polychromatic418967fa.accept_7_6_5_4_1_297
  125 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 152 284 4 31 38 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 152 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 123 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 152 284 2 61 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 152 284 (accept_3_2 121 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 152 284 4 30 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 152 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 119 152 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 152 284 2 59 76 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 152 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 117 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 152 284 4 29 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 152 284 (accept_3_2 115 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 152 284 2 57 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 152 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 113 152 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 152 284 4 28 38 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 152 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 111 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 152 284 2 55 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 152 284 (accept_3_2 109 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 152 284 4 27 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 152 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 107 152 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 152 284 2 53 76 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 152 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 105 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 152 284 4 26 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 152 284 (accept_3_2 103 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 152 284 2 51 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 152 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 101 152 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 152 284 4 25 38 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 152 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 99 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 152 284 2 49 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 152 284 (accept_3_2 97 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 152 284 4 24 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 152 284 (Polychromatic418967fa.accept_15_5_2_14_1_1693 95 152 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 152 284 2 47 76 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 152 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 93 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 152 284 4 23 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 152 284 (accept_3_2 91 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 152 284 2 45 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 152 284 (Polychromatic418967fa.accept_16_9_8_12_1_979 89 152 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 152 284 4 22 38 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 87 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 152 284 2 43 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 152 284 (accept_3_2 85 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 152 284 4 21 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 152 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 284 2 41 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 284
  (Polychromatic418967fa.accept_16_1_8_12_1_405 81 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 284 4 20 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 284 (accept_3_2 79 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 284 2 39 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 284 4 19 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 152 284 2 37 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 152 284 (accept_3_2 73 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 284 4 18 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 152 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 284 2 35 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 284 4 17 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 284 (accept_3_2 67 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 284 2 33 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 284 4 16 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 284
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 63 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 284 2 31 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 284 (accept_3_2 61 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 284 4 15 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 284 (Polychromatic418967fa.accept_13_7_9_11_1_705 59 152 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 284 2 29 76 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 284 4 14 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 284 (accept_3_2 55 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 284 2 27 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 284 (Polychromatic418967fa.accept_13_1_9_11_1_703 53 152 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 284 4 13 38 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 284 2 25 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 284 (accept_3_2 49 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 284 4 12 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 284 2 23 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 284
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 152 284 4 11 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 152 284 (accept_3_2 43 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 284 2 21 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 284 4 10 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 284 2 19 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 284 (accept_3_2 37 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 284 4 9 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 152 284 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 152 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 284 2 17 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 33
  152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 284 4 8 38 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 284 (accept_3_2 31
  152 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 284 2 15 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 152 284 4 7 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 152 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 152 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 284 2 13 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 284 (accept_3_2 25 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 284 4 6 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 152 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 284 2 11 76 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 284 4 5 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 152 284 (accept_3_2 19 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  152 284 2 9 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 152 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 284 4 4 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 284 2 7 76 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 284 (accept_3_2 13
  152 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 284 4 3 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 284 2 5 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 152 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 284 4 2 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 284 (accept_3_2 7 152 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 284 2 3 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 284 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 152 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 284 4 1 38 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 152 284 2 1 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 152 284 (accept_3_2 1 152 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 151 284 (Eq.refl Bool.true) (allA_of_3_0 134 151 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 135 150 284 (Eq.refl Bool.true) (allA_succ_of_gcd 134 150 284 2 67 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 150 284 (accept_3_2 133 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 150 284 2 66 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 150 284 (Polychromatic418967fa.accept_13_1_7_11_1_702
  131 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 150 284 2 65 75 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 150 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 129 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 150 284 2 64 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 150 284 (accept_3_2 127 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 150 284 2 63 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 150 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 125 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 150 284 2 62 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 150 284
  (Polychromatic418967fa.accept_11_2_7_9_1_890 123 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 150 284 2 61 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 150 284 (accept_3_2 121 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 150 284 2 60 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 150 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 119 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 150 284 2 59 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 150 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 117 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 150 284 2 58 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 150 284 (accept_3_2 115 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 150 284 2 57 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 150 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 113 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 150 284 2 56 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 150 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 111 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 150 284 2 55 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 150 284 (accept_3_2 109 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 150 284 2 54 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 150 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 107 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 150 284 2 53 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 150 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 105 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 150 284 2 52 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 150 284 (accept_3_2 103 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 150 284 2 51 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 150 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 101 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 150 284 2 50 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 150 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 99 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 150 284 2 49 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 150 284 (accept_3_2 97 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 150 284 2 48 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 150 284 (Polychromatic418967fa.accept_13_4_7_11_1_1981 95 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 150 284 2 47 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 150 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 93 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 150 284 2 46 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 150 284 (accept_3_2 91 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 150 284 2 45 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 150 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 89 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 150 284 2 44 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 150 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 150 284 2 43 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 150 284 (accept_3_2 85 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 150 284 2 42 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 150 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 150 284 2 41 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 150 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 150 284 2 40 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 150 284 (accept_3_2 79 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 284 2 39 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 284 (Polychromatic418967fa.accept_13_12_7_11_1_1935 77 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 284 2 38 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 150 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 150 284 2 37 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 150 284 (accept_3_2 73 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 284 2 36 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 284 2 35 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 150 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 150 284 2 34 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 150 284 (accept_3_2 67 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 284 2 33 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 150 284 2 32 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 284 2 31 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 284 (accept_3_2 61 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 284 2 30 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 284 (Polychromatic418967fa.accept_27_5_15_14_1_17408 59 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 284 2 29 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 284 2 28 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 150 284 (accept_3_2 55 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 284 2 27 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 284 2 26 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 284 2 25 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 284 (accept_3_2 49 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 284 2 24 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 284 2 23 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 150 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 150 284 2 22 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 150 284 (accept_3_2 43 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 284 2 21 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 284 2 20 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 284 2 19 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 284 (accept_3_2 37 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 284 2 18 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 284 2 17 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 284 2 16 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 284 (accept_3_2 31 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 284 2 15 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 284 2 14 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 284 2 13 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 284 (accept_3_2 25 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 284 2 12 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 284 (Polychromatic418967fa.accept_19_4_17_18_1_9536 23 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 284 2 11 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 284 2 10 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 284 (accept_3_2 19 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 284 2 9 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 284 2 8 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 284 2 7 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 284 (accept_3_2 13 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 284 2 6 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 150 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 284 2 5 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 284 2 4 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 284 (accept_3_2 7 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  284 2 3 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  150 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 150 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 284 2 2 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 150 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 150 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 284 2 1 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 284 (accept_3_2 1 150 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 136 149 284 (Eq.refl Bool.true) (allA_succ_of_accept 135 149 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 135 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 149 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 134 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 149 284 (accept_3_2 133 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 149 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 132 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 149 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 131 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 149 284 (accept_3_2 130 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 129 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 149 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 128 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 149 284 (accept_3_2 127 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 149 284 (Polychromatic418967fa.accept_25_1_24_9_1_17407 126
  149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 149 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 125 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 149 284 (accept_3_2 124 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 149 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 122 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 149 284 (accept_3_2 121 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 149 284 (Polychromatic418967fa.accept_16_8_5_12_1_3812 120
  149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 149 284
  (Polychromatic418967fa.accept_16_7_5_12_1_4824 119 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 149 284 (accept_3_2 118 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 149 284 (Polychromatic418967fa.accept_16_4_5_12_1_2749 116
  149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 149 284 (accept_3_2 115
  149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 149 284
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 114 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 149 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 113 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 149 284 (accept_3_2 112 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 149 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 110 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 149 284 (accept_3_2 109 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 149 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 108 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 149 284 (Polychromatic418967fa.accept_22_19_17_20_1_14411 107 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 149 284 (accept_3_2 106 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 149
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 149 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 104 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 149 284 (accept_3_2 103 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 149 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 102 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 149 284 (Polychromatic418967fa.accept_17_16_13_12_1_4092 101 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 149 284 (accept_3_2 100 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 149 284
  (Polychromatic418967fa.accept_10_8_9_4_1_961 98 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 149 284 (accept_3_2 97 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 149 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 149 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 95 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 149 284 (accept_3_2 94 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 149 284
  (Polychromatic418967fa.accept_22_4_17_20_1_9804 92 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 149 284 (accept_3_2 91 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 149 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 149 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 149 284 (accept_3_2 88 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87
  149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 149 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 149 284 (accept_3_2 85 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 149 284 (Polychromatic418967fa.accept_16_4_5_12_1_2749 84 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 149 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 284 (accept_3_2 82 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 284
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 80 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 149 284 (accept_3_2 79 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 149 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 78 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 149 284 (Polychromatic418967fa.accept_21_14_2_11_1_8625 77 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 284 (accept_3_2 76 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 149 284 (accept_3_2 73 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 149 284 (Polychromatic418967fa.accept_14_2_9_4_1_1735 72 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 149 284 (Polychromatic418967fa.accept_16_7_5_12_1_4824 71 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 284 (accept_3_2 70 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 149 284 (accept_3_2 67 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 149 284 (Polychromatic418967fa.accept_19_9_16_18_1_3887 66 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 149 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 284 (accept_3_2 64 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 284 (accept_3_2 61 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 284 (Polychromatic418967fa.accept_13_8_6_11_1_1979 60 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 284 (Polychromatic418967fa.accept_19_2_16_18_1_10922 59 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 284 (accept_3_2 58 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 284
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 56 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 284 (accept_3_2 55 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 53 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 284 (accept_3_2 52 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 284 (accept_3_2 49 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 284 (accept_3_2 46 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 284
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 44 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 284 (accept_3_2 43 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 284 (Polychromatic418967fa.accept_16_10_5_12_1_4925 42 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 284 (accept_3_2 40 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 284
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 284 (accept_3_2 37 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 284 (accept_3_2 34 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 284
  (Polychromatic418967fa.accept_19_13_16_18_1_10882 32 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 149 284 (accept_3_2 31 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 149 284 (Polychromatic418967fa.accept_13_4_6_11_1_2017 30 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 284 (Polychromatic418967fa.accept_18_11_5_14_1_4560 29 149
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 284 (accept_3_2 28 149
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 149 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 284 (accept_3_2 25 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 149 284 (Polychromatic418967fa.accept_16_8_5_12_1_3812 24 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 284
  (Polychromatic418967fa.accept_10_3_9_4_1_960 23 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 284 (accept_3_2 22 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 284 (accept_3_2 19 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 284 (accept_3_2 16 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 284 (accept_3_2 13 149 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 284
  (Polychromatic418967fa.accept_17_11_13_12_1_1968 11 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 149 284 (accept_3_2 10 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 284 (accept_3_2 7 149 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6
  149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 284 (accept_3_2 4 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 284 (accept_3_2 1 149 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 137 148 284 (Eq.refl Bool.true) (allA_of_3_0 137 148 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 138 147 284 (Eq.refl Bool.true) (allA_succ_of_accept 137 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 137 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 147 284 (accept_3_2 136 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  135 147 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 135 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 134 147 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 134 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 147 284 (accept_3_2 133 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 132 147
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 131 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 147 284 (accept_3_2 130 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 147 284 (Polychromatic418967fa.accept_13_12_4_11_1_1925 129 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 128 147 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 128 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 147 284 (accept_3_2 127 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 147 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 126 147
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 147 284 (accept_3_2 124 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 123 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 147 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 122 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 147 284 (accept_3_2 121 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 147 284 (Polychromatic418967fa.accept_16_8_3_12_1_1819 120
  147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 147 284 (accept_3_2 118 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 147 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 117 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 116 147 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 116 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 147 284 (accept_3_2 115 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 114 147
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 147 284 (accept_3_2 112 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 147 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 111 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 147 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 110 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 147 284 (accept_3_2 109 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 147 284 (Polychromatic418967fa.accept_14_10_7_4_1_3453 108
  147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 147 284 (accept_3_2 106 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 147 284 (Polychromatic418967fa.accept_16_8_3_12_1_1819 104 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 284 (accept_3_2 103 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 147 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 102 147
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 147 284 (accept_3_2 100 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 147 284 (Polychromatic418967fa.accept_13_8_4_11_1_3469 99 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 147 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 147 284 (accept_3_2 97 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 147 284 (accept_3_2 94 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 147 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 93 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 147 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 92 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 284 (accept_3_2 91 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 147 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 90 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 147 284 (accept_3_2 88 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 147 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 147 284 (Polychromatic418967fa.accept_13_8_4_11_1_3469 86 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 284 (accept_3_2 85 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 147 284 (Polychromatic418967fa.accept_13_6_4_11_1_282 84 147
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 147 284 (accept_3_2 82 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 147 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 81 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 147 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 284 (accept_3_2 79 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 147 284 (accept_3_2 76 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 147 284 (Polychromatic418967fa.accept_13_10_4_11_1_1969 75 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 147 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 284 (accept_3_2 73 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 284 (accept_3_2 70 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 147 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 68 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 284 (accept_3_2 67 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 147
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 284 (accept_3_2 64 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 147 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 284 (accept_3_2 61 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 284 (accept_3_2 58 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 57 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 147 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 284 (accept_3_2 55 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 284 (accept_3_2 52 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 284 (Polychromatic418967fa.accept_17_16_11_12_1_2008 50 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 284 (accept_3_2 49 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 284 (Polychromatic418967fa.accept_17_14_11_12_1_4109 48
  147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 284 (accept_3_2 46 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 284 (Polychromatic418967fa.accept_13_6_4_11_1_282 45 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 284 (accept_3_2 43 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 284 (accept_3_2 40 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 284 (accept_3_2 37 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 284 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 147 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 284 (accept_3_2 34 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 284 (accept_3_2 31 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 147
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 284 (accept_3_2 28 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 284 (accept_3_2 25 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 284 (accept_3_2 22 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 284 (accept_3_2 19 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 284 (accept_3_2 16 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 284 (Polychromatic418967fa.accept_17_14_11_12_1_4109 14 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 284 (accept_3_2 13 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 147
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 284 (accept_3_2 10 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 284 (accept_3_2 7 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 147 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 284 (accept_3_2 4 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 147 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 284 (accept_3_2 1 147 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 139 146 284 (Eq.refl Bool.true) (allA_succ_of_gcd 138 146 284 2 69 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 137 146 284
  (Polychromatic418967fa.accept_12_5_2_8_1_172 137 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 136 146 284 2 68 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 135 146 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 135 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 146 284 2 67 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 146 284 (accept_3_2 133 146 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 146 284 2 66 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 146 284 (Polychromatic418967fa.accept_7_5_6_4_1_117
  131 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 146 284 2 65 73 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 146 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 129 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 146 284 2 64 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 146 284 (accept_3_2 127 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 146 284 2 63 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 146 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 125 146 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 146 284 2 62 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 146 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 123 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 146 284 2 61 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 146 284 (accept_3_2 121 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 146 284 2 60 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 146 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 119 146 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 146 284 2 59 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 146 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 117 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 146 284 2 58 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 146 284 (accept_3_2 115 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 146 284 2 57 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 146 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 113 146 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 146 284 2 56 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 146 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 111 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 146 284 2 55 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 146 284 (accept_3_2 109 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 146 284 2 54 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 146 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 107 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 146 284 2 53 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 146 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 105 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 146 284 2 52 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 146 284 (accept_3_2 103 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 146 284 2 51 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 146 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 101 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 146 284 2 50 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 146 284
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 99 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 146 284 2 49 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 146 284 (accept_3_2 97 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 146 284 2 48 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 146 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 95 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 146 284 2 47 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 146 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 93 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 146 284 2 46 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 146 284 (accept_3_2 91 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 146 284 2 45 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 146 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 89 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 284 2 44 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 87 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 284 2 43 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 284 (accept_3_2 85 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 284 2 42 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 83 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 284 2 41 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 284
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 81 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 284 2 40 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 284 (accept_3_2 79 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 284 2 39 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 284 2 38 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 284 2 37 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 284 (accept_3_2 73 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 284 2 36 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 284 2 35 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 69 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 284 2 34 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 284 (accept_3_2 67 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 284 2 33 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 284 2 32 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 284
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 146 284 2 31 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 146 284 (accept_3_2 61 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 284 2 30 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 284 2 29 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 284 2 28 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 284 (accept_3_2 55 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 284 2 27 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 284 2 26 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 284 2 25 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 284 (accept_3_2 49 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 284 2 24 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 284 2 23 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 284 2 22 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 284 (accept_3_2 43 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 284 2 21 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 284 2 20 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 284 2 19 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 284 (accept_3_2 37 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 284 2 18 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 284 2 17 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 284 2 16 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 284 (accept_3_2 31 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 284 2 15 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 284 2 14 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 284
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 284 2 13 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 284 (accept_3_2 25 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 284 2 12 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 284 2 11 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 284 2 10 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 284 (accept_3_2 19 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 284 2 9 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 146 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 284 2 8 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 284 2 7 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 284 (accept_3_2 13 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 284 2 6 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 146 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 284 2 5 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 284 2 4 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 284 (accept_3_2 7 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  284 2 3 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 146 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 284 2 2 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 146 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 284 2 1 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 284 (accept_3_2 1 146 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 140 145 284 (Eq.refl Bool.true) (allA_of_3_0 140 145 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 141 144 284 (Eq.refl Bool.true) (allA_succ_of_gcd 140 144 284 4 35 36 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 139 144 284 (accept_3_2 139 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 138 144 284 2 69 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 137 144 284 (Polychromatic418967fa.accept_13_7_1_11_1_732
  137 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 144 284 4 34 36 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 144 284
  (Polychromatic418967fa.accept_21_9_18_11_1_8644 135 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 134 144 284 2 67 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 133 144 284 (accept_3_2 133 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 144 284 4 33 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 144 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 131 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 144 284 2 65 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 144 284
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 129 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 128 144 284 4 32 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 127 144 284 (accept_3_2 127 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 144 284 2 63 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 144 284 (Polychromatic418967fa.accept_13_8_1_11_1_1284 125 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 144 284 4 31 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 144 284
  (Polychromatic418967fa.accept_17_4_8_12_1_9165 123 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 122 144 284 2 61 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 121 144 284 (accept_3_2 121 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 144 284 4 30 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 144 284 (Polychromatic418967fa.accept_21_14_18_11_1_3961 119 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 144 284 2 59 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 144 284
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 117 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 144 284 4 29 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 144 284 (accept_3_2 115 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 144 284 2 57 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 144 284 (Polychromatic418967fa.accept_13_9_1_11_1_275 113 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 144 284 4 28 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 144 284
  (Polychromatic418967fa.accept_13_7_1_11_1_732 111 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 144 284 2 55 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 144 284 (accept_3_2 109 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 144 284 4 27 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 144 284 (Polychromatic418967fa.accept_13_3_1_11_1_1268 107 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 144 284 2 53 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 144 284
  (Polychromatic418967fa.accept_17_3_8_12_1_6573 105 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 144 284 4 26 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 144 284 (accept_3_2 103 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 144 284 2 51 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 144 284 (Polychromatic418967fa.accept_13_10_1_11_1_1961 101 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 144 284 4 25 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 144 284
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 99 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 144 284 2 49 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 144 284 (accept_3_2 97 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 144 284 4 24 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 144 284 (Polychromatic418967fa.accept_15_5_9_14_1_1724 95 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 144 284 2 47 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 144 284
  (Polychromatic418967fa.accept_19_17_11_18_1_9533 93 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 144 284 4 23 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 144 284 (accept_3_2 91 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 144 284 2 45 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 144 284 (Polychromatic418967fa.accept_17_4_8_12_1_9165 89 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 144 284 4 22 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 144 284
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 87 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 144 284 2 43 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 144 284 (accept_3_2 85 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 284 4 21 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 284 (Polychromatic418967fa.accept_15_8_9_14_1_4577 83 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 284 2 41 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 144 284
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 81 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 144 284 4 20 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 144 284 (accept_3_2 79 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 284 2 39 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 284 (Polychromatic418967fa.accept_13_12_1_11_1_1917 77 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 284 4 19 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 144 284
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 75 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 144 284 2 37 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 144 284 (accept_3_2 73 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 284 4 18 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 284 (Polychromatic418967fa.accept_17_3_8_12_1_6573 71 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 284 2 35 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 144 284
  (Polychromatic418967fa.accept_19_12_11_18_1_10844 69 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 144 284 4 17 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 144 284 (accept_3_2 67 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 284 2 33 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 65 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 284 4 16 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 284
  (Polychromatic418967fa.accept_19_6_11_18_1_12181 63 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 144 284 2 31 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 144 284 (accept_3_2 61 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 284 4 15 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 284 (Polychromatic418967fa.accept_13_7_1_11_1_732 59 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 284 2 29 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 284
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 144 284 4 14 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 144 284 (accept_3_2 55 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 284 2 27 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 284 (Polychromatic418967fa.accept_15_8_9_14_1_4577 53 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 284 4 13 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 284
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 51 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 144 284 2 25 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 144 284 (accept_3_2 49 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 284 4 12 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 284 (Polychromatic418967fa.accept_13_8_1_11_1_1284 47 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 284 2 23 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 284
  (Polychromatic418967fa.accept_19_7_11_18_1_6680 45 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 144 284 4 11 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 144 284 (accept_3_2 43 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 284 2 21 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 284 (Polychromatic418967fa.accept_19_3_11_18_1_2709 41 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 284 4 10 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 284
  (Polychromatic418967fa.accept_17_5_8_12_1_6609 39 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 284 2 19 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 284 (accept_3_2 37 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 284 4 9 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 284 (Polychromatic418967fa.accept_13_9_1_11_1_275 35 144 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 284 2 17 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 284 (Polychromatic418967fa.accept_13_7_1_11_1_732
  33 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 284 4 8 36 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 284
  (accept_3_2 31 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 284 2 15 72 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 284
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 29 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 284 4 7 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 144 284 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 144 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 284 2 13 72 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 284 (accept_3_2 25 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 284 4 6 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 284
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 144 284 2 11 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 144 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 284 4 5 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 284 (accept_3_2 19 144 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 284 2 9 72 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 284
  (Polychromatic418967fa.accept_19_17_11_18_1_9533 17 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 144 284 4 4 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 144 284 (Polychromatic418967fa.accept_23_15_6_8_1_17406 15 144 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 284 2 7 72 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 284 (accept_3_2 13
  144 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 284 4 3 36 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 284
  (Polychromatic418967fa.accept_25_11_19_9_1_15765 11 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 144 284 2 5 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 144 284 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 284 4 2 36 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 284 (accept_3_2 7 144 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 284 2 3 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 284 (Polychromatic418967fa.accept_15_5_9_14_1_1724
  5 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 284 4 1 36 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 284
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 144 284 2 1 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 144 284 (accept_3_2 1 144 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 142 143 284 (Eq.refl Bool.true) (allA_succ_of_accept 141 143 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 141 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 140 143 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 140 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 139 143 284 (accept_3_2 139 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 138 143 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 138 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 143 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 137 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 143 284 (accept_3_2 136 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  135 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 135 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 134 143 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 134 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 143 284 (accept_3_2 133 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 143 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 132 143
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 143 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 131 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 143 284 (accept_3_2 130 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 129 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 143 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 128 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 143 284 (accept_3_2 127 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 143 284 (Polychromatic418967fa.accept_15_6_8_14_1_4575 126
  143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 143 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 125 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 143 284 (accept_3_2 124 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 143 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 122 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 143 284 (accept_3_2 121 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 143 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 120 143
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 143 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 119 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 143 284 (accept_3_2 118 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 143 284 (Polychromatic418967fa.accept_16_4_15_12_1_1745 116 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 143 284 (accept_3_2 115 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 143 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 114 143
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 143 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 113 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 143 284 (accept_3_2 112 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 143 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 110 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 143 284 (accept_3_2 109 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 143 284 (Polychromatic418967fa.accept_24_12_23_20_1_14124 108
  143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 143 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 107 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 143 284 (accept_3_2 106 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 143 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 104 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 143 284 (accept_3_2 103 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 143 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 143
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 143 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 101 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 143 284 (accept_3_2 100 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 143 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 98 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 143 284 (accept_3_2 97 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 143 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 143 284
  (Polychromatic418967fa.accept_15_5_8_14_1_432 95 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 143 284 (accept_3_2 94 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 143 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 92 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 284 (accept_3_2 91 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 284
  (Polychromatic418967fa.accept_10_9_3_4_1_985 89 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 143 284 (accept_3_2 88 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 143 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 86 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 284 (accept_3_2 85 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 83 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 143 284 (accept_3_2 82 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 143 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 80 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 284 (accept_3_2 79 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 284
  (Polychromatic418967fa.accept_10_7_3_4_1_978 77 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 143 284 (accept_3_2 76 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 143 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 284 (accept_3_2 73 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 284 (Polychromatic418967fa.accept_16_8_15_12_1_1747 72 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 143 284 (accept_3_2 70 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 143 284 (Polychromatic418967fa.accept_16_4_15_12_1_1745 68 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 284 (accept_3_2 67 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 143 284 (accept_3_2 64 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 143 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 284 (accept_3_2 61 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 284 (accept_3_2 58 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 284 (accept_3_2 55 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 284 (Polychromatic418967fa.accept_15_9_8_14_1_1699 54 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 284
  (Polychromatic418967fa.accept_17_2_7_12_1_1078 53 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 284 (accept_3_2 52 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 284 (accept_3_2 49 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 284 (accept_3_2 46 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 284 (Polychromatic418967fa.accept_21_2_17_11_1_7037 44 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 284 (accept_3_2 43 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 284 (accept_3_2 40 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 284 (accept_3_2 37 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 284 (accept_3_2 34 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 284 (Polychromatic418967fa.accept_26_6_13_24_1_17405 32 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 284 (accept_3_2 31 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 284 (accept_3_2 28 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 284 (accept_3_2 25 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 284
  (Polychromatic418967fa.accept_21_2_17_11_1_7037 23 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 143 284 (accept_3_2 22 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 143 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 284 (accept_3_2 19 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 284
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 284 (accept_3_2 16 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 284 (accept_3_2 13 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 284 (accept_3_2 10 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 284 (accept_3_2 7 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 284 (accept_3_2 4 143 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 284 (accept_3_2 1 143 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 142 284 (allA_of_3_0 142 142 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 141 284
  (allA_succ_of_accept 140 141 284 (Polychromatic418967fa.accept_15_5_6_14_1_1721 140 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 139 141 284 (accept_3_2 139 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 138 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 138 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 137 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 141 284 (accept_3_2 136 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  135 141 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 135 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 134 141 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 134 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 141 284 (accept_3_2 133 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 141 284 (Polychromatic418967fa.accept_16_4_13_12_1_1740 132
  141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 131 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 141 284 (accept_3_2 130 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 129 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 141 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 128 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 141 284 (accept_3_2 127 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 141 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 126 141
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 141 284 (accept_3_2 124 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 141 284 (Polychromatic418967fa.accept_14_11_1_4_1_4445 123 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 122 141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 122 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 141 284 (accept_3_2 121 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 141 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 120 141
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 141 284 (accept_3_2 118 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 117 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 141 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 116 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 141 284 (accept_3_2 115 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 141 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 114 141
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 141 284 (accept_3_2 112 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 141 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 111 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 110 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 284 (accept_3_2 109 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 108 141
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 141 284 (accept_3_2 106 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 141 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 105 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 141 284 (Polychromatic418967fa.accept_16_8_13_12_1_3809 104 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 284 (accept_3_2 103 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 141 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 141
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 141 284 (accept_3_2 100 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 141 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627 99 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 141 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 284 (accept_3_2 97 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 141 284 (accept_3_2 94 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 141 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 141 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 284 (accept_3_2 91 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 141 284 (accept_3_2 88 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 141 284 (Polychromatic418967fa.accept_19_10_8_18_1_2669 86 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 284 (accept_3_2 85 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 141 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 284 (accept_3_2 82 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 141 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 80 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 284 (accept_3_2 79 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 284 (accept_3_2 76 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 141 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 284 (accept_3_2 73 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 284 (Polychromatic418967fa.accept_16_8_13_12_1_3809 72 141 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 284 (accept_3_2 70 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 141 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627 69 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 284 (accept_3_2 67 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 284 (accept_3_2 64 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 284 (Polychromatic418967fa.accept_16_15_13_12_1_1787 63 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 284 (accept_3_2 61 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 284 (Polychromatic418967fa.accept_17_9_5_12_1_6606 60 141
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 284 (accept_3_2 58 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 284 (accept_3_2 55 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 284 (accept_3_2 52 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 284 (Polychromatic418967fa.accept_19_13_8_18_1_10905 51 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 284 (Polychromatic418967fa.accept_15_5_6_14_1_1721 50 141 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 284 (accept_3_2 49 141 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 48
  141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 284 (accept_3_2 46 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 284 (accept_3_2 43 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 284 (accept_3_2 40 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 284 (accept_3_2 37 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 284 (Polychromatic418967fa.accept_16_4_13_12_1_1740 36 141 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 284 (accept_3_2 34 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 284 (Polychromatic418967fa.accept_19_13_8_18_1_10905 32 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 284 (accept_3_2 31 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 141 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 284 (accept_3_2 28 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 284 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 284 (accept_3_2 25 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 284 (accept_3_2 22 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 284 (accept_3_2 19 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 284 (accept_3_2 16 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 284 (Polychromatic418967fa.accept_22_14_9_20_1_17404 14 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 284 (accept_3_2 13 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 284 (accept_3_2 10 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 284 (accept_3_2 7 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 141 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 284 (accept_3_2 4 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 141 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 284 (accept_3_2 1 141 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 140 284 (allA_succ_of_accept 139 140 284 (accept_3_2 139 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 138 140 284 2 69 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 137 140 284 (Polychromatic418967fa.accept_15_2_5_14_1_61 137 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 140 284 4 34 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 140 284
  (Polychromatic418967fa.accept_22_3_8_20_1_11418 135 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 134 140 284 2 67 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 133 140 284 (accept_3_2 133 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 140 284 4 33 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 140 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 131 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 140 284 2 65 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 140 284
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 129 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 128 140 284 4 32 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 127 140 284 (accept_3_2 127 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 140 284 2 63 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 140 284 (Polychromatic418967fa.accept_13_8_10_11_1_2730 125 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 140 284 4 31 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 140 284
  (Polychromatic418967fa.accept_21_18_14_11_1_7035 123 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 122 140 284 2 61 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 121 140 284 (accept_3_2 121 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 140 284 4 30 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 140 284 (Polychromatic418967fa.accept_13_2_10_11_1_1276 119 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 140 284 2 59 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 140 284
  (Polychromatic418967fa.accept_21_12_14_11_1_3921 117 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 140 284 4 29 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 140 284 (accept_3_2 115 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 140 284 2 57 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 140 284 (Polychromatic418967fa.accept_15_8_5_14_1_986 113 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 140 284 4 28 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 140 284
  (Polychromatic418967fa.accept_15_6_5_14_1_429 111 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 140 284 2 55 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 140 284 (accept_3_2 109 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 140 284 4 27 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 140 284 (Polychromatic418967fa.accept_13_3_10_11_1_1293 107 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 140 284 2 53 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 140 284
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 105 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 140 284 4 26 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 140 284 (accept_3_2 103 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 140 284 2 51 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 140 284 (Polychromatic418967fa.accept_19_6_7_18_1_120 101 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 140 284 4 25 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 140 284
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 99 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 140 284 2 49 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 140 284 (accept_3_2 97 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 140 284 4 24 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 140 284 (Polychromatic418967fa.accept_13_4_10_11_1_1908 95 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 140 284 2 47 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 140 284
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 93 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 140 284 4 23 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 140 284 (accept_3_2 91 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 140 284 2 45 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 140 284 (Polychromatic418967fa.accept_21_5_14_11_1_10102 89 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 140 284 4 22 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 140 284
  (Polychromatic418967fa.accept_11_10_8_9_1_492 87 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 140 284 2 43 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 140 284 (accept_3_2 85 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 140 284 4 21 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 140 284 (Polychromatic418967fa.accept_15_8_5_14_1_986 83 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 284 2 41 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 284
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 81 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 140 284 4 20 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 140 284 (accept_3_2 79 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 140 284 2 39 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 140 284 (Polychromatic418967fa.accept_13_12_10_11_1_1279 77 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 284 4 19 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 140 284
  (Polychromatic418967fa.accept_17_7_4_12_1_4084 75 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 140 284 2 37 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 140 284 (accept_3_2 73 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 140 284 4 18 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 140 284 (Polychromatic418967fa.accept_19_14_7_18_1_12160 71 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 284 2 35 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 284
  (Polychromatic418967fa.accept_13_4_10_11_1_1908 69 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 140 284 4 17 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 140 284 (accept_3_2 67 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 284 2 33 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 140 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 65 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 284 4 16 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 284
  (Polychromatic418967fa.accept_19_6_7_18_1_120 63 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 140 284 2 31 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 140 284 (accept_3_2 61 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 284 4 15 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 284 (Polychromatic418967fa.accept_17_8_4_12_1_1994 59 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 284 2 29 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 284
  (Polychromatic418967fa.accept_26_5_10_24_1_12004 57 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 140 284 4 14 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 140 284 (accept_3_2 55 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 284 2 27 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 284 (Polychromatic418967fa.accept_13_1_10_11_1_1280 53 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 284 4 13 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 284
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 51 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 140 284 2 25 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 140 284 (accept_3_2 49 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 284 4 12 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 284 (Polychromatic418967fa.accept_13_8_10_11_1_2730 47 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 284 2 23 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 284
  (Polychromatic418967fa.accept_21_3_14_11_1_14578 45 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 140 284 4 11 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 140 284 (accept_3_2 43 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 284 2 21 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 284 (Polychromatic418967fa.accept_13_2_10_11_1_1276 41 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 284 4 10 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 284
  (Polychromatic418967fa.accept_15_9_5_14_1_973 39 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 284 2 19 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 284 (accept_3_2 37 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 284 4 9 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 140 284 (Polychromatic418967fa.accept_25_10_15_9_1_17403 35 140 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 284 2 17 70 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 284
  (Polychromatic418967fa.accept_19_14_7_18_1_12160 33 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 140 284 4 8 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 140 284 (accept_3_2 31 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 284 2 15 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 284 (Polychromatic418967fa.accept_13_3_10_11_1_1293 29 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 284 4 7 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 284
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 140 284 2 13 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 140 284 (accept_3_2 25 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 284 4 6 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 140 284 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 140 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 284 2 11 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 284 (Polychromatic418967fa.accept_11_10_8_9_1_492
  21 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 140 284 4 5 35 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 284
  (accept_3_2 19 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 140 284 2 9 70 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 140 284
  (Polychromatic418967fa.accept_13_4_10_11_1_1908 17 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 140 284 4 4 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 140 284 (Polychromatic418967fa.accept_13_2_10_11_1_1276 15 140 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 284 2 7 70 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 284 (accept_3_2 13
  140 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 284 4 3 35 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 284
  (Polychromatic418967fa.accept_19_11_7_18_1_5284 11 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 140 284 2 5 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 140 284 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 284 4 2 35 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 284 (accept_3_2 7 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 284 2 3 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 140 284
  (Polychromatic418967fa.accept_21_5_14_11_1_10102 5 140 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 284 4 1 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 140 284 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 140 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 284 2 1 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 284 (accept_3_2 1 140 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 139 284 (allA_of_3_0 139 139 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 138 284
  (allA_succ_of_accept 137 138 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 137 138 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 138 284 2 68 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 138 284 (Polychromatic418967fa.accept_7_2_5_4_1_115
  135 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 138 284 2 67 69 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 138 284
  (accept_3_2 133 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 138 284 2 66 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 138 284
  (Polychromatic418967fa.accept_13_1_8_11_1_724 131 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 138 284 2 65 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 138 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 129 138 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 138 284 2 64 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 138 284 (accept_3_2 127 138 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 138 284 2 63 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 138 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 125 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 138 284 2 62 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 138 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 123 138 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 138 284 2 61 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 138 284 (accept_3_2 121 138 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 138 284 2 60 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 138 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 119 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 138 284 2 59 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 138 284 (Polychromatic418967fa.accept_12_9_6_8_1_518 117 138 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 138 284 2 58 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 138 284 (accept_3_2 115 138 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 138 284 2 57 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 138 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 113 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 138 284 2 56 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 138 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 111 138 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 138 284 2 55 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 138 284 (accept_3_2 109 138 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 138 284 2 54 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 138 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 107 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 138 284 2 53 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 138 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 138 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 138 284 2 52 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 138 284 (accept_3_2 103 138 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 138 284 2 51 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 138 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 101 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 138 284 2 50 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 138 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 99 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 138 284 2 49 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 138 284 (accept_3_2 97 138 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 138 284 2 48 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 138 284 (Polychromatic418967fa.accept_13_4_8_11_1_1937
  95 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 138 284 2 47 69 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 138 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 93 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 138 284 2 46 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 138 284 (accept_3_2 91 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 284 2 45 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 89 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 138 284 2 44 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 138 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 87 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 138 284 2 43 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 138 284 (accept_3_2 85 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 284 2 42 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 284 2 41 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 138 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 138 284 2 40 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 284 (accept_3_2 79 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 284 2 39 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 77 138 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 284 2 38 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 138 284 2 37 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 284 (accept_3_2 73 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 284 2 36 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 284 2 35 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 138 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 138 284 2 34 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 284 (accept_3_2 67 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 284 2 33 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 284 2 32 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 284 2 31 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 284 (accept_3_2 61 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 284 2 30 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 284 2 29 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 284 2 28 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 284 (accept_3_2 55 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 284 2 27 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 284 2 26 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 284 2 25 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 284 (accept_3_2 49 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 284 2 24 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 284 2 23 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 284 2 22 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 284 (accept_3_2 43 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 284 2 21 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 284 2 20 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 284 2 19 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 284 (accept_3_2 37 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 284 2 18 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 284 2 17 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 284 2 16 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 284 (accept_3_2 31 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 284 2 15 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 284 2 14 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 284 2 13 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 284 (accept_3_2 25 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 284 2 12 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 284 2 11 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 284 2 10 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 284 (accept_3_2 19 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 284 2 9 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 284 2 8 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 284 2 7 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 284 (accept_3_2 13 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 284 2 6 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 138 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 284 2 5 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 284 2 4 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 284 (accept_3_2 7 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  284 2 3 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 284 (Polychromatic418967fa.accept_16_5_10_12_1_4904 5 138 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 284 2 2 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 138 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 284 2 1 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 284 (accept_3_2 1 138 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 137 284 (allA_succ_of_accept 136 137 284 (accept_3_2 136 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 135 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 135 137 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 137 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 134 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 137 284 (accept_3_2 133 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 137 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 132 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 137 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 131 137 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 137 284 (accept_3_2 130 137 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 129 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 137 284
  (Polychromatic418967fa.accept_11_7_5_9_1_884 128 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 137 284 (accept_3_2 127 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  126 137 284 (Polychromatic418967fa.accept_13_9_7_11_1_1292 126 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 125 137 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 125 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 137 284 (accept_3_2 124 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 137 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 122 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 137 284 (accept_3_2 121 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 137 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 120 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 137 284 (Polychromatic418967fa.accept_14_7_11_4_1_3455 119 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 137 284 (accept_3_2 118 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 137 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 116 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 137 284 (accept_3_2 115 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 137 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 114 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 137 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 113 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 137 284 (accept_3_2 112 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 137 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 110 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 137 284 (accept_3_2 109 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 137 284 (Polychromatic418967fa.accept_13_4_7_11_1_1981 108 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 137 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 107 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 137 284 (accept_3_2 106 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 137 284
  (Polychromatic418967fa.accept_16_8_9_12_1_1737 104 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 137 284 (accept_3_2 103 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 137 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 137 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 137 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 101 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 137 284 (accept_3_2 100 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 137 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 99 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 137 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 137 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 284 (accept_3_2 97 137 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 137 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 137 284 (Polychromatic418967fa.accept_11_7_5_9_1_884
  95 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 137 284 (accept_3_2 94
  137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 137 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 93 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 137 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 92 137 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 284 (accept_3_2 91 137 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 137 284 (Polychromatic418967fa.accept_13_12_7_11_1_1935 90 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 137 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 89 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 137 284 (accept_3_2 88 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 137 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 86 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 284 (accept_3_2 85 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 137 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 284
  (Polychromatic418967fa.accept_10_3_7_4_1_584 83 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 284 (accept_3_2 82 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 137 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 284 (accept_3_2 79 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 284
  (Polychromatic418967fa.accept_8_5_1_4_1_628 77 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 137 284 (accept_3_2 76 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 137 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 284 (accept_3_2 73 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 137 284 (accept_3_2 70 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 137 284 (Polychromatic418967fa.accept_13_3_7_11_1_1904 68 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 284 (accept_3_2 67 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 137 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 284
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 284 (accept_3_2 64 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 284 (accept_3_2 61 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 284
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 59 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 137 284 (accept_3_2 58 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 284 (Polychromatic418967fa.accept_13_4_7_11_1_1981 56 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 284 (accept_3_2 55 137
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 284
  (Polychromatic418967fa.accept_26_2_7_24_1_10154 54 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 284 (accept_3_2 52 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 284 (accept_3_2 49 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 284 (Polychromatic418967fa.accept_17_13_1_12_1_7893 47 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 284 (accept_3_2 46 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 284 (accept_3_2 43 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 41 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 284 (accept_3_2 40 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 137 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 284 (accept_3_2 37 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 284 (accept_3_2 34 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 284 (accept_3_2 31 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 284 (accept_3_2 28 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 284 (accept_3_2 25 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 284 (accept_3_2 22 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 284
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 284 (accept_3_2 19 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 284 (accept_3_2 16 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 284 (accept_3_2 13 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 284 (accept_3_2 10 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 284 (accept_3_2 7 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 284 (accept_3_2 4 137 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 284 (accept_3_2 1 137 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 136 284 (allA_of_3_0 136 136 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 135 284
  (allA_succ_of_accept 134 135 284 (Polychromatic418967fa.accept_19_1_2_18_1_10827 134 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 135 284 (accept_3_2 133 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 132 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 132 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 131 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 135 284 (accept_3_2 130 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 135 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 129 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 135 284 (Polychromatic418967fa.accept_14_2_9_4_1_1735 128 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 135 284 (accept_3_2 127 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 135 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 126 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 135 284 (accept_3_2 124 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 135 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 123 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 135 284 (Polychromatic418967fa.accept_20_2_15_4_1_7575 122 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 135 284 (accept_3_2 121 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 135 284 (Polychromatic418967fa.accept_13_3_5_11_1_716 120 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 135 284 (accept_3_2 118 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 135 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 117 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 135 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 116 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 135 284 (accept_3_2 115 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 135 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 114 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 135 284 (accept_3_2 112 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 111 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 135 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 110 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 135 284 (accept_3_2 109 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 135 284 (Polychromatic418967fa.accept_25_8_10_9_1_17402 108
  135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 135 284 (accept_3_2 106 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 135 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 105 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 104 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 284 (accept_3_2 103 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 135 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 102 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 135 284 (accept_3_2 100 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 135 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 99 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 135 284 (Polychromatic418967fa.accept_13_7_5_11_1_1927 98 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 284 (accept_3_2 97 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 135 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 135 284 (accept_3_2 94 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 135 284 (Polychromatic418967fa.accept_18_3_9_14_1_2219 93 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 135 284 (Polychromatic418967fa.accept_19_16_2_18_1_8136 92 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 284 (accept_3_2 91 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 135 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 135 284 (accept_3_2 88 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 135 284 (Polychromatic418967fa.accept_30_27_15_14_1_17401 87 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 86 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 284 (accept_3_2 85 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 284 (Polychromatic418967fa.accept_13_6_5_11_1_1971 84 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 284 (accept_3_2 82 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 135 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 81 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 135 284 (Polychromatic418967fa.accept_19_4_2_18_1_6662 80 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 284 (accept_3_2 79 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 284 (accept_3_2 76 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 135 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 135 284 (Polychromatic418967fa.accept_22_8_3_20_1_8170 74 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 284 (accept_3_2 73 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 135 284 (accept_3_2 70 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 135 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 284 (accept_3_2 67 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 135 284 (accept_3_2 64 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 135 284 (Polychromatic418967fa.accept_22_19_3_20_1_11394 63 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 284 (accept_3_2 61 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 284 (Polychromatic418967fa.accept_18_6_9_14_1_9915 60 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 284 (accept_3_2 58 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 284 (Polychromatic418967fa.accept_18_3_9_14_1_2219 57 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 284 (accept_3_2 55 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 135 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 284 (accept_3_2 52 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 50 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 284 (accept_3_2 49 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 135 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 284 (accept_3_2 46 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 284 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 284 (Polychromatic418967fa.accept_14_2_9_4_1_1735 44 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 284 (accept_3_2 43 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 284 (accept_3_2 40 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 284 (Polychromatic418967fa.accept_22_16_3_20_1_908 38 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 284 (accept_3_2 37 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 284 (accept_3_2 34 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 284 (Polychromatic418967fa.accept_13_6_5_11_1_1971 32 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 284 (accept_3_2 31 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 135
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 284 (accept_3_2 28 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 284 (accept_3_2 25 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 284 (Polychromatic418967fa.accept_16_8_7_12_1_7207 24 135 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 284 (accept_3_2 22 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 284 (accept_3_2 19 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 284 (accept_3_2 16 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 284 (Polychromatic418967fa.accept_19_15_2_18_1_6699 15 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 284 (Polychromatic418967fa.accept_31_14_11_5_1_17400 14 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 284 (accept_3_2 13 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 284 (accept_3_2 10 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 284 (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 284 (accept_3_2 7 135 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 135 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 284 (accept_3_2 4 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 135 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 284 (Polychromatic418967fa.accept_14_2_9_4_1_1735 2 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 284 (accept_3_2 1 135 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 134 284 (allA_succ_of_accept 133 134 284 (accept_3_2 133 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 134 284 2 66 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 134 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 131 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 134 284 2 65 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 134 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 129 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 134 284 2 64 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 134 284 (accept_3_2 127 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 134 284 2 63 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 134 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 125 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 134 284 2 62 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 134 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 123 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 134 284 2 61 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 134 284 (accept_3_2 121 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 134 284 2 60 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 134 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 119 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 134 284 2 59 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 134 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 117 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 134 284 2 58 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 134 284 (accept_3_2 115 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 134 284 2 57 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 134 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 113 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 134 284 2 56 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 134 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 111 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 134 284 2 55 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 134 284 (accept_3_2 109 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 134 284 2 54 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 134 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 107 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 134 284 2 53 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 134 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 105 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 134 284 2 52 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 134 284 (accept_3_2 103 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 134 284 2 51 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 134 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 101 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 134 284 2 50 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 134 284
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 99 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 134 284 2 49 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 134 284 (accept_3_2 97 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 134 284 2 48 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 134 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 95 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 134 284 2 47 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 134 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 93 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 134 284 2 46 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 134 284 (accept_3_2 91 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 134 284 2 45 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 134 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 134 284 2 44 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 134 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 87 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 134 284 2 43 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 134 284 (accept_3_2 85 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 134 284 2 42 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 134 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 284 2 41 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 284
  (Polychromatic418967fa.accept_11_4_2_9_1_496 81 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 284 2 40 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 284 (accept_3_2 79 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 284 2 39 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 284 2 38 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 284 2 37 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 284 (accept_3_2 73 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 284 2 36 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 284 2 35 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 284 2 34 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 284 (accept_3_2 67 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 284 2 33 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 284 2 32 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 284
  (Polychromatic418967fa.accept_19_6_1_18_1_13556 63 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 134 284 2 31 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 134 284 (accept_3_2 61 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 284 2 30 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 284 2 29 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 284 2 28 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 284 (accept_3_2 55 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 284 2 27 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 284 2 26 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 284 2 25 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 284 (accept_3_2 49 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 284 2 24 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 284 2 23 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 284 2 22 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 284 (accept_3_2 43 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 284 2 21 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 284 2 20 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 284 2 19 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 284 (accept_3_2 37 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 284 2 18 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 284 2 17 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 284 2 16 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 284 (accept_3_2 31 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 284 2 15 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 284 2 14 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 284
  (Polychromatic418967fa.accept_19_8_1_18_1_5240 27 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 284 2 13 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 284 (accept_3_2 25 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 284 2 12 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 284 2 11 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 284 2 10 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 284 (accept_3_2 19 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 284 2 9 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 284 2 8 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 284 2 7 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 284 (accept_3_2 13 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 284 2 6 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 134 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 284 2 5 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 284
  (Polychromatic418967fa.accept_20_9_14_4_1_4540 9 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 284 2 4 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 284 (accept_3_2 7 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  284 2 3 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 134 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 284 2 2 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 134 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 284 2 1 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 284 (accept_3_2 1 134 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 133 284 (allA_of_3_0 133 133 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 132 284
  (allA_succ_of_accept 131 132 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 131 132 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 132 284 2 65 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 132 284 (Polychromatic418967fa.accept_7_3_6_4_1_30
  129 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 132 284 4 32 33 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 132 284
  (accept_3_2 127 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 132 284 2 63 66 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 132 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 125 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 132 284 4 31 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 132 284 (Polychromatic418967fa.accept_16_11_4_12_1_1760 123 132 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 132 284 2 61 66 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 132 284 (accept_3_2 121 132 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 132 284 4 30 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 132 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 119 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 132 284 2 59 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 132 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 117 132 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 132 284 4 29 33 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 132 284 (accept_3_2 115 132 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 132 284 2 57 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 132 284
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 113 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 132 284 4 28 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 111 132 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 111 132 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 132 284 2 55 66 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 132 284 (accept_3_2 109 132 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 284 4 27 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 107 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 132 284 2 53 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 132 284 (Polychromatic418967fa.accept_16_9_4_12_1_4896 105 132 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 132 284 4 26 33 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 284 (accept_3_2 103 132 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 132 284 2 51 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 132 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 101 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 132 284 4 25 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 132 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 99 132 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 132 284 2 49 66 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 284 (accept_3_2 97 132 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 132 284 4 24 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 132 284
  (Polychromatic418967fa.accept_13_4_2_11_1_733 95 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 284 2 47 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 132 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 284 4 23 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 284 (accept_3_2 91 132 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 132 284 2 45 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 132 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 89
  132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 132 284 4 22 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 132 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 87 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 132 284 2 43 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 132 284 (accept_3_2 85 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 284 4 21 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 284 2 41 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 284
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 81 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 284 4 20 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 284 (accept_3_2 79 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 284 2 39 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 284 4 19 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 284 2 37 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 284 (accept_3_2 73 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 284 4 18 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 284 2 35 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 284
  (Polychromatic418967fa.accept_13_4_2_11_1_733 69 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 132 284 4 17 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 132 284 (accept_3_2 67 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 284 2 33 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 284 4 16 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 284
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 132 284 2 31 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 132 284 (accept_3_2 61 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 284 4 15 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 284 2 29 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 284 4 14 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 284 (accept_3_2 55 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 284 2 27 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 284 4 13 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 284 2 25 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 284 (accept_3_2 49 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 284 4 12 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 284 2 23 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 284 4 11 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 132 284 (accept_3_2 43 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 284 2 21 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 284 (Polychromatic418967fa.accept_15_11_12_14_1_2612 41 132 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 284 4 10 33 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 284 2 19 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 284 (accept_3_2 37 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 284 4 9 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 132 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 284 2 17 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 284 4 8 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 284 (accept_3_2 31
  132 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 284 2 15 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 284 4 7 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 132 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 284 2 13 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 284 (accept_3_2 25 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 284 4 6 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 132 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 284 2 11 66 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 284 4 5 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 284 (accept_3_2 19 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  132 284 2 9 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 132 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 284 4 4 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 284
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 284 2 7 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 284 (accept_3_2 13 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 284 4 3 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 132 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 284 2 5 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9
  132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 284 4 2 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 284 (accept_3_2 7
  132 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 284 2 3 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 132 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 132 284 4 1 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 132 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 284 2 1 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 284 (accept_3_2 1 132 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 132
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 131 284 (allA_succ_of_accept 130 131 284 (accept_3_2 130 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 129 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 131 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 128 131
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 131 284 (accept_3_2 127 131
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 131 284
  (Polychromatic418967fa.accept_13_9_1_11_1_275 126 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 131 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 125 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 131 284 (accept_3_2 124 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 131 284
  (Polychromatic418967fa.accept_11_1_10_9_1_871 122 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 131 284 (accept_3_2 121 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 131 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 120 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 131 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 119 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 131 284 (accept_3_2 118 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 131
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 131 284
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 116 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 131 284 (accept_3_2 115 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 131 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 114 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 131 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 113 131
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 131 284 (accept_3_2 112 131
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 131 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 111 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 131 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 110 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 131 284 (accept_3_2 109 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 131 284 (Polychromatic418967fa.accept_15_3_11_14_1_1705 108 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 131 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 107 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 131 284 (accept_3_2 106 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 131 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 104 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 131 284 (accept_3_2 103 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 131 284 (Polychromatic418967fa.accept_15_12_11_14_1_3464 102
  131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 131 284
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 101 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 131 284 (accept_3_2 100 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 131 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 98 131
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 131 284 (accept_3_2 97 131
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 131 284
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 96 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 131 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 95 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 131 284 (accept_3_2 94 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 131 284 (Polychromatic418967fa.accept_7_1_5_4_1_134
  92 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 284 (accept_3_2 91
  131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 131 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 90 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 131 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 89 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 131 284 (accept_3_2 88 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 284 (Polychromatic418967fa.accept_7_2_5_4_1_115
  86 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 284 (accept_3_2 85
  131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 284
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 84 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 131 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 284 (accept_3_2 82 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 284
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 80 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 131 284 (accept_3_2 79 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 131 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 131 284 (Polychromatic418967fa.accept_10_7_1_4_1_1447 77 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 284 (accept_3_2 76 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 284
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 74 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 284 (accept_3_2 73 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 284 (accept_3_2 70 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 284
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 68 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 284 (accept_3_2 67 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 284 (Polychromatic418967fa.accept_25_16_6_9_1_10586 66 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 284 (accept_3_2 64 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 284 (accept_3_2 61 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 284 (Polychromatic418967fa.accept_13_8_1_11_1_1284 60 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 284 (Polychromatic418967fa.accept_13_7_1_11_1_732 59 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 284 (accept_3_2 58 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 284
  (Polychromatic418967fa.accept_11_1_10_9_1_871 56 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 284 (accept_3_2 55 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 284 (Polychromatic418967fa.accept_19_16_17_18_1_2688 54 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 284 (Polychromatic418967fa.accept_20_13_11_4_1_2042 53 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 284 (accept_3_2 52 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 284 (accept_3_2 49 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 284 (accept_3_2 46 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 284 (accept_3_2 43 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 284 (Polychromatic418967fa.accept_13_3_1_11_1_1268 42 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 284 (accept_3_2 40 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 284 (accept_3_2 37 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 284 (accept_3_2 34 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 284
  (Polychromatic418967fa.accept_19_13_17_18_1_6638 32 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 131 284 (accept_3_2 31 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 131 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 131 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 284 (accept_3_2 28 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 284 (accept_3_2 25 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 284 (Polychromatic418967fa.accept_16_8_3_12_1_1819 24 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 284 (accept_3_2 22 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 284 (accept_3_2 19 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 284 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 284 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 284 (accept_3_2 16 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 284 (accept_3_2 13 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 284 (Polychromatic418967fa.accept_18_11_5_14_1_4560 11 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 284 (accept_3_2 10 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 284 (accept_3_2 7 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 284 (accept_3_2 4 131 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 284 (accept_3_2 1 131 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 130 284 (allA_of_3_0 130 130 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 129 284
  (allA_succ_of_accept 128 129 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 128 129 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 129 284 (accept_3_2 127 129 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 129 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 126 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 129 284 (accept_3_2 124 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 123 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 129 284 (Polychromatic418967fa.accept_20_2_9_4_1_4539 122 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 129 284 (accept_3_2 121 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 129 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 120 129
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 129 284 (accept_3_2 118 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 129 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 117 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 129 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 116 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 284 (accept_3_2 115 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 114 129
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 129 284 (accept_3_2 112 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 129 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 111 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 129 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 110 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 284 (accept_3_2 109 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 108 129
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 129 284 (accept_3_2 106 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 129 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 104 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 284 (accept_3_2 103 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 102 129
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 129 284 (accept_3_2 100 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 129 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 129 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 284 (accept_3_2 97 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 284 (accept_3_2 94 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 129 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 93 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 129 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 92 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 284 (accept_3_2 91 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 284 (accept_3_2 88 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 129 284 (Polychromatic418967fa.accept_23_17_14_8_1_11171 86 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 284 (accept_3_2 85 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 284 (Polychromatic418967fa.accept_16_4_1_12_1_1792 84 129
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 129 284 (accept_3_2 82 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 129 284 (Polychromatic418967fa.accept_15_6_9_14_1_3457 81 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 129 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 284 (accept_3_2 79 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 284 (accept_3_2 76 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 129 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 75 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 129 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 284 (accept_3_2 73 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 284 (Polychromatic418967fa.accept_13_7_12_11_1_1911 72 129 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 284 (accept_3_2 70 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 129 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 129 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 68 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 284 (accept_3_2 67 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 129
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 284 (accept_3_2 64 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 129 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 129 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 284 (accept_3_2 61 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 284 (accept_3_2 58 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 129 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 129 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 284 (accept_3_2 55 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 284 (accept_3_2 52 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 284 (accept_3_2 49 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 284 (accept_3_2 46 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 284 (accept_3_2 43 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 284 (accept_3_2 40 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 284 (Polychromatic418967fa.accept_17_5_10_12_1_6545 39 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 284 (accept_3_2 37 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 284 (accept_3_2 34 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 32 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 284 (accept_3_2 31 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 129
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 284 (accept_3_2 28 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 284 (accept_3_2 25 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 284 (accept_3_2 22 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 284 (accept_3_2 19 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 284 (accept_3_2 16 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 284 (Polychromatic418967fa.accept_13_1_12_11_1_728 14 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 284 (accept_3_2 13 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 284 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 129
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 284 (accept_3_2 10 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 284 (accept_3_2 7 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 129 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 284 (accept_3_2 4 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 129 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 284 (accept_3_2 1 129 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 284 (allA_succ_of_accept 127 128 284 (accept_3_2 127 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 128 284 2 63 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 128 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 125 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 128 284 4 31 32 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 128 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 123 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 128 284 2 61 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 128 284 (accept_3_2 121 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 128 284 4 30 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 128 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 119 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 128 284 2 59 64 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 128 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 117 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 128 284 4 29 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 128 284 (accept_3_2 115 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 128 284 2 57 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 128 284 (Polychromatic418967fa.accept_23_21_13_8_1_15940 113 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 128 284 4 28 32 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 128 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 111 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 128 284 2 55 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 128 284 (accept_3_2 109 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 128 284 4 27 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 128 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 107 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 128 284 2 53 64 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 128 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 105 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 128 284 4 26 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 128 284 (accept_3_2 103 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 128 284 2 51 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 128 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 101 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 128 284 4 25 32 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 128 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 99 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 128 284 2 49 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 128 284 (accept_3_2 97 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 128 284 4 24 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 128 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 95 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 128 284 2 47 64 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 128 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 93 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 128 284 4 23 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 128 284 (accept_3_2 91 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 128 284 2 45 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 128 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 128 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 128 284 4 22 32 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 128 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 87 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 128 284 2 43 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 128 284 (accept_3_2 85 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 128 284 4 21 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 128 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 128 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 284 2 41 64 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 284
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 81 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 128 284 4 20 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 128 284 (accept_3_2 79 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 128 284 2 39 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 128 284 (Polychromatic418967fa.accept_19_1_14_18_1_3919 77 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 284 4 19 32 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 128 284 2 37 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 128 284 (accept_3_2 73 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 128 284 4 18 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 128 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 128 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 284 2 35 64 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 284 4 17 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 284 (accept_3_2 67 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 284 2 33 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814 65 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 284 4 16 32 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 284
  (Polychromatic418967fa.accept_24_15_8_20_1_12559 63 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 128 284 2 31 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 128 284 (accept_3_2 61 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 284 4 15 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 128 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 284 2 29 64 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 284 4 14 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 284 (accept_3_2 55 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 284 2 27 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 128 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 284 4 13 32 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 284 2 25 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 284 (accept_3_2 49 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 284 4 12 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 128 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 284 2 23 64 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 284
  (Polychromatic418967fa.accept_19_7_14_18_1_6654 45 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 128 284 4 11 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 128 284 (accept_3_2 43 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 284 2 21 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 128 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 284 4 10 32 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 284 2 19 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 284 (accept_3_2 37 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 284 4 9 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 128 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 128 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 284 2 17 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 284 4 8 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 284 (accept_3_2 31
  128 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 284 2 15 64 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 29 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 128 284 4 7 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 128 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 128 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 284 2 13 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 284 (accept_3_2 25 128 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 284 4 6 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 128
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 284 2 11 64 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 284 4 5 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 128 284 (accept_3_2 19 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  128 284 2 9 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 128 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 284 4 4 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 284 2 7 64 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 284 (accept_3_2 13
  128 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 284 4 3 32 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 284
  (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 128 284 2 5 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 128 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 284 4 2 32 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 284 (accept_3_2 7 128 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 284 2 3 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5
  128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 284 4 1 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 128 284 2 1 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 128 284 (accept_3_2 1 128 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 127 284 (allA_of_3_0 127 127 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 126 284
  (allA_succ_of_accept 125 126 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 125 126 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 126 284 2 62 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 126 284 (Polychromatic418967fa.accept_12_3_6_8_1_969
  123 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 126 284 2 61 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 126 284
  (accept_3_2 121 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 126 284 2 60 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 126 284
  (Polychromatic418967fa.accept_13_2_9_11_1_258 119 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 126 284 2 59 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 126 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 117 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 126 284 2 58 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 126 284 (accept_3_2 115 126 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 126 284 2 57 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 126 284
  (Polychromatic418967fa.accept_15_8_6_14_1_975 113 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 126 284 2 56 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 126 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 111 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 126 284 2 55 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 126 284 (accept_3_2 109 126 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 126 284 2 54 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 126 284
  (Polychromatic418967fa.accept_17_5_7_12_1_1951 107 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 126 284 2 53 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 126 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 105 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 126 284 2 52 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 126 284 (accept_3_2 103 126 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 126 284 2 51 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 126 284
  (Polychromatic418967fa.accept_19_6_12_18_1_8141 101 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 126 284 2 50 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 126 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 126 284 2 49 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 126 284 (accept_3_2 97 126 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 126 284 2 48 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 126 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 95 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 126 284 2 47 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 126 284 (Polychromatic418967fa.accept_12_9_6_8_1_518 93 126 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 126 284 2 46 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 126 284 (accept_3_2 91 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 126 284 2 45 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 126 284 (Polychromatic418967fa.accept_17_4_7_12_1_6556
  89 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 284 2 44 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 284 2 43 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 284 (accept_3_2 85 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 284 2 42 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 284 (Polychromatic418967fa.accept_15_8_6_14_1_975 83 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 284 2 41 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 284 2 40 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 284 (accept_3_2 79 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 284 2 39 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 284 (Polychromatic418967fa.accept_19_1_12_18_1_10820 77 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 284 2 38 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 75 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 284 2 37 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 284 (accept_3_2 73 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 284 2 36 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 284 (Polychromatic418967fa.accept_17_3_7_12_1_2016 71 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 284 2 35 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 284 2 34 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 284 (accept_3_2 67 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 284 2 33 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 126 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 284 2 32 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 126 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 126 284 2 31 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 284 (accept_3_2 61 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 284 2 30 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 284 (Polychromatic418967fa.accept_13_7_9_11_1_705 59 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 284 2 29 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 284 2 28 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 284 (accept_3_2 55 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 284 2 27 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 284 (Polychromatic418967fa.accept_13_1_9_11_1_703 53 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 284 2 26 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 284
  (Polychromatic418967fa.accept_11_7_5_9_1_884 51 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 284 2 25 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 284 (accept_3_2 49 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 284 2 24 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 284 (Polychromatic418967fa.accept_13_8_9_11_1_1265 47 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 284 2 23 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 284 2 22 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 284 (accept_3_2 43 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 284 2 21 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 284 (Polychromatic418967fa.accept_13_2_9_11_1_258 41 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 284 2 20 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 284 2 19 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 284 (accept_3_2 37 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 284 2 18 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 126 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 284 2 17 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 284 2 16 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 284 (accept_3_2 31 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 284 2 15 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 126 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 284 2 14 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 284 2 13 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 284 (accept_3_2 25 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 284 2 12 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 284 (Polychromatic418967fa.accept_15_8_6_14_1_975 23 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 284 2 11 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 284 2 10 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 284 (accept_3_2 19 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 284 2 9 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 284 (Polychromatic418967fa.accept_19_17_12_18_1_5248 17 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 284 2 8 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 284 2 7 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 284 (accept_3_2 13 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 284 2 6 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 284 (Polychromatic418967fa.accept_19_11_12_18_1_3893 11 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 284 2 5 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 284 2 4 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 284 (accept_3_2 7 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126
  284 2 3 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 126 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 284 2 2 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 126 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 126 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 284 2 1 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 284 (accept_3_2 1 126 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 284 (allA_succ_of_accept 124 125 284 (accept_3_2 124 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 125 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 125 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 122 125
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 125 284 (accept_3_2 121 125
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 125 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 120 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 125 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 119 125 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 125 284 (accept_3_2 118 125 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 125 284
  (Polychromatic418967fa.accept_10_6_5_4_1_571 116 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 125 284 (accept_3_2 115 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 125 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 114 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 125 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 113 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 284 (accept_3_2 112 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 125
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 125 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 110 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 125 284 (accept_3_2 109 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 125 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 125 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 107 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 284 (accept_3_2 106 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 125
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 125 284
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 104 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 125 284 (accept_3_2 103 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 125 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 125 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 101 125
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 125 284 (accept_3_2 100 125
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 125 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 99 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 125 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 98 125 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 284 (accept_3_2 97 125 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 125 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 125 284
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 95 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 125 284 (accept_3_2 94 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 125 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 92 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 284 (accept_3_2 91 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 90 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 125 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 89 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 284 (accept_3_2 88 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 125 284 (accept_3_2 85 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 125 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 284 (accept_3_2 82 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 125 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 125 284 (accept_3_2 79 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 284
  (Polychromatic418967fa.accept_15_2_5_14_1_61 77 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 284 (accept_3_2 76 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 125 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 284 (accept_3_2 73 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 125 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 284
  (Polychromatic418967fa.accept_10_1_5_4_1_276 71 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 125 284 (accept_3_2 70 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 125 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 284 (accept_3_2 67 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 125 284 (accept_3_2 64 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 125 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 284 (accept_3_2 61 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 125 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 284 (accept_3_2 58 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 284 (accept_3_2 55 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 284
  (Polychromatic418967fa.accept_13_1_8_11_1_724 53 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 284 (accept_3_2 52 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 284 (accept_3_2 49 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 125 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 284 (accept_3_2 46 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 284 (accept_3_2 43 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 284 (accept_3_2 40 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 284 (accept_3_2 37 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 284
  (Polychromatic418967fa.accept_11_2_4_9_1_484 35 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 284 (accept_3_2 34 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 284 (Polychromatic418967fa.accept_13_6_8_11_1_5398 32 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 284 (accept_3_2 31 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 125 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 284 (accept_3_2 28 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 284 (accept_3_2 25 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 284 (accept_3_2 22 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 284 (accept_3_2 19 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 284 (Polychromatic418967fa.accept_17_1_6_12_1_1944 18 125 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 284 (accept_3_2 16 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 284 (accept_3_2 13 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 125 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 284 (accept_3_2 10 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 284 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 284 (accept_3_2 7 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 125 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 284 (accept_3_2 4 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 284 (accept_3_2 1 125 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 124 284 (allA_of_3_0 124 124 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 123 284
  (allA_succ_of_accept 122 123 284 (Polychromatic418967fa.accept_13_5_6_11_1_1933 122 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 123 284 (accept_3_2 121 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 120 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 120 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 123 284 (accept_3_2 118 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 123 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 117 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 123 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 116 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 123 284 (accept_3_2 115 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 114 123
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 123 284 (accept_3_2 112 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 123 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 111 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 123 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 110 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 284 (accept_3_2 109 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 284 (Polychromatic418967fa.accept_13_4_6_11_1_2017 108
  123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 123 284 (accept_3_2 106 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 123 284 (Polychromatic418967fa.accept_14_7_11_4_1_3455 105 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 123 284 (Polychromatic418967fa.accept_16_8_11_12_1_962 104 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 284 (accept_3_2 103 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63
  102 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 123 284 (accept_3_2 100 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 123 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 99 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 123 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 284 (accept_3_2 97 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 284 (Polychromatic418967fa.accept_13_5_6_11_1_1933 96 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 284 (accept_3_2 94 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 123 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 284 (accept_3_2 91 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 284 (accept_3_2 88 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 284 (Polychromatic418967fa.accept_13_8_6_11_1_1979 86 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 284 (accept_3_2 85 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 284 (accept_3_2 82 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 123 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 81 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 123 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 284 (accept_3_2 79 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 284 (accept_3_2 76 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 123 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 284 (accept_3_2 73 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 284 (Polychromatic418967fa.accept_16_8_11_12_1_962 72 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 284 (accept_3_2 70 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 123 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 69 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 123 284 (Polychromatic418967fa.accept_16_4_11_12_1_1775 68 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 284 (accept_3_2 67 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 284 (accept_3_2 64 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 284 (accept_3_2 61 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 284 (Polychromatic418967fa.accept_13_8_6_11_1_1979 60 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 284 (accept_3_2 58 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 284 (accept_3_2 55 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 284 (accept_3_2 52 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 50 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 284 (accept_3_2 49 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 284 (accept_3_2 46 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 284 (Polychromatic418967fa.accept_21_3_18_11_1_10061 45 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 284 (accept_3_2 43 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 123
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 284 (accept_3_2 40 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 284 (accept_3_2 37 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 284 (accept_3_2 34 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 284 (Polychromatic418967fa.accept_16_1_11_12_1_1774 33 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 32 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 284 (accept_3_2 31 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 284 (accept_3_2 28 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 284 (accept_3_2 25 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 284 (Polychromatic418967fa.accept_16_8_11_12_1_962 24 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 284 (accept_3_2 22 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 284 (accept_3_2 19 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 284 (accept_3_2 16 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 284 (Polychromatic418967fa.accept_20_14_3_4_1_11915 14 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 284 (accept_3_2 13 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 123 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 284 (accept_3_2 10 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 284 (accept_3_2 7 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 123 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 284 (accept_3_2 4 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 123 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 284 (accept_3_2 1 123 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_284_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


