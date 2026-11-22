-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch286_Segment001
-- name    : Polychromatic418967fa_Branch286_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:58:41.528363+00:00
-- url     : https://prove2.me/theorems/0ab80acb-ea20-4e77-bc85-fe5c1489d616
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch286_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_286_segment_001 : allB 183 286 :=
  allB_succ' 105 182 286 (Eq.refl Bool.true) (allA_of_3_1 105 182 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 181 286 (Eq.refl Bool.true) (allA_succ_of_accept 105 181 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 181 286 (accept_3_3 104 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 181 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 181 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 102 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 181 286 (accept_3_3 101 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 181 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 100 181
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 181 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 181 286 (accept_3_3 98 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 181 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 97 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 181 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 181 286 (accept_3_3 95 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 181 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 181 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 181 286 (accept_3_3 92 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 181 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 181 286 (Polychromatic418967fa.accept_16_10_5_14_1_6173 90 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 181 286 (accept_3_3 89 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 181 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 88 181
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 181 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 181 286 (accept_3_3 86 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 181 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 181 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 181 286 (accept_3_3 83 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 181 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 82 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 181 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 181 286 (accept_3_3 80 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 181 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 181 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 181 286 (accept_3_3 77 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 181 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 181 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 181 286 (accept_3_3 74 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 181 286 (Polychromatic418967fa.accept_16_9_5_14_1_6126 73 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 181 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 181 286 (accept_3_3 71 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 181 286 (Polychromatic418967fa.accept_19_13_10_1_1_8236 70 181
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 181 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 181 286 (accept_3_3 68 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 181 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 181 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 181 286 (accept_3_3 65 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 181 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 181 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 181 286 (accept_3_3 62 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 181 286 (Polychromatic418967fa.accept_14_5_13_6_1_3574 61 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 181 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 181 286 (accept_3_3 59 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 181 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 181 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 181 286 (accept_3_3 56 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 181 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 181 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 286 (accept_3_3 53 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 181 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 181
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 286 (accept_3_3 50 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 286 (accept_3_3 47 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 286 (Polychromatic418967fa.accept_17_12_11_14_1_3120 46 181 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 286 (accept_3_3 44 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 286 (accept_3_3 41 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 286 (accept_3_3 38 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 286 (Polychromatic418967fa.accept_19_17_10_1_1_6795 36 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 286 (accept_3_3 35 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 286 (Polychromatic418967fa.accept_20_14_1_6_1_3352 34 181
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 286 (accept_3_3 32 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 286 (accept_3_3 29 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 286 (accept_3_3 26 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 286 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 286 (accept_3_3 23 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 286 (accept_3_3 20 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 286 (Polychromatic418967fa.accept_25_18_6_11_1_12487 18 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 286 (accept_3_3 17 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 181
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 286 (accept_3_3 14 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 286 (accept_3_3 11 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 286 (Polychromatic418967fa.accept_16_10_5_14_1_6173 10 181 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 286 (accept_3_3 8 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 286 (accept_3_3 5 181 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 181 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 286 (accept_3_3 2 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 286 (Polychromatic418967fa.accept_23_1_20_10_1_9665 1 181 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 180 286 (Eq.refl Bool.true) (allA_succ_of_gcd 106 180 286 2 53 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 180 286
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 105 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 180 286 2 52 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 180 286 (Polychromatic418967fa.accept_16_7_4_14_1_2860 103 180 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 180 286 2 51 90 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 180 286 (accept_3_3
  101 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 180 286 2 50 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 180 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 180 286 2 49 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 180 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 97 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 180 286 2 48 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 180 286 (accept_3_3 95 180 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 180 286 2 47 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 180 286
  (Polychromatic418967fa.accept_19_17_9_1_1_12360 93 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 180 286 2 46 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 180 286 (Polychromatic418967fa.accept_25_16_5_11_1_17592 91 180 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 180 286 2 45 90 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 180 286 (accept_3_3 89
  180 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 180 286 2 44 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 180 286
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 87 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 180 286 2 43 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 180 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 180 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 180 286 2 42 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 180 286 (accept_3_3 83 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 180 286 2 41 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 180 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 81
  180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 180 286 2 40 90 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 180 286
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 79 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 180 286 2 39 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 180 286 (accept_3_3 77 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 180 286 2 38 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 180 286 (Polychromatic418967fa.accept_17_7_10_14_1_8022 75 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 180 286 2 37 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 180 286
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 73 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 180 286 2 36 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 180 286 (accept_3_3 71 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 180 286 2 35 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 180 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 69 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 180 286 2 34 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 180 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 286 2 33 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 180 286 (accept_3_3 65 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 180 286 2 32 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 180 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 63 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 180 286 2 31 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 180 286
  (Polychromatic418967fa.accept_23_15_19_10_1_17591 61 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 180 286 2 30 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 180 286 (accept_3_3 59 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 180 286 2 29 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 180 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 180 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 180 286 2 28 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 180 286
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 55 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 180 286 2 27 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 180 286 (accept_3_3 53 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 180 286 2 26 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 180 286 (Polychromatic418967fa.accept_21_9_12_13_1_16221 51 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 180 286 2 25 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 286
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 49 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 286 2 24 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 286 (accept_3_3 47 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 180 286 2 23 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 180 286 (Polychromatic418967fa.accept_21_3_12_13_1_8816 45 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 180 286 2 22 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 286 2 21 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 286 (accept_3_3 41 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 180 286 2 20 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 180 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 180 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 180 286 2 19 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 286
  (Polychromatic418967fa.accept_23_14_19_10_1_14323 37 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 180 286 2 18 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 180 286 (accept_3_3 35 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 180 286 2 17 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 180 286 (Polychromatic418967fa.accept_16_1_4_14_1_1896 33 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 180 286 2 16 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 286
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 31 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 180 286 2 15 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 180 286 (accept_3_3 29 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 180 286 2 14 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 180 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 180 286 2 13 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 286 2 12 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 286 (accept_3_3 23 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 180 286 2 11 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 180 286 (Polychromatic418967fa.accept_19_2_9_1_1_4029 21 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 286 2 10 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 286
  (Polychromatic418967fa.accept_25_19_5_11_1_17590 19 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 180 286 2 9 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 180 286 (accept_3_3 17 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 286 2 8 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 180 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 180 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 286 2 7 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 286
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 180 286 2 6 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 180 286 (accept_3_3 11 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 286 2 5 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 180 286 (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 180 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 286 2 4 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 286
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 286 2 3 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 286 (accept_3_3 5 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180
  286 2 2 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  180 286 (Polychromatic418967fa.accept_21_3_12_13_1_8816 3 180 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 180 286 2 1 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 180 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 180 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 179 286 (Eq.refl Bool.true) (allA_of_3_1 108 179 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 178 286 (Eq.refl Bool.true) (allA_succ_of_gcd 108 178 286 2 54 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 178 286 (accept_3_3 107 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 178 286 2 53 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 178 286
  (Polychromatic418967fa.accept_19_10_7_1_1_1685 105 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 178 286 2 52 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 178 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 103 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 178 286 2 51 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 178 286 (accept_3_3 101 178 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 178 286 2 50 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 178 286
  (Polychromatic418967fa.accept_19_4_7_1_1_1683 99 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 178 286 2 49 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 178 286 (Polychromatic418967fa.accept_19_2_7_1_1_2808 97 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 178 286 2 48 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 178 286 (accept_3_3 95 178 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 178 286 2 47 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 178 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 93 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 178 286 2 46 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 178 286 (Polychromatic418967fa.accept_17_6_8_14_1_6706 91 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 178 286 2 45 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 178 286 (accept_3_3 89 178 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 178 286 2 44 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 178 286
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 87 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 178 286 2 43 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 178 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 85 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 178 286 2 42 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 178 286 (accept_3_3 83 178 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 178 286 2 41 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 178 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 178 286 2 40 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 178 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 178 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 178 286 2 39 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 178 286 (accept_3_3 77 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 178 286 2 38 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 178 286 (Polychromatic418967fa.accept_17_7_8_14_1_6720
  75 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 178 286 2 37 89 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 178 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 178 286 2 36 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 178 286 (accept_3_3 71 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 178 286 2 35 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 178 286 (Polychromatic418967fa.accept_19_12_7_1_1_5400 69 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 178 286 2 34 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 178 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 178 286 2 33 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 178 286 (accept_3_3 65 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 178 286 2 32 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 178 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 178 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 178 286 2 31 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 178 286
  (Polychromatic418967fa.accept_19_4_7_1_1_1683 61 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 178 286 2 30 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 178 286 (accept_3_3 59 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 178 286 2 29 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 178 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 57 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 178 286 2 28 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 178 286
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 178 286 2 27 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 178 286 (accept_3_3 53 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 178 286 2 26 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 178 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 178 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 286 2 25 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 286
  (Polychromatic418967fa.accept_21_7_10_13_1_4093 49 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 178 286 2 24 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 178 286 (accept_3_3 47 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 286 2 23 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 286 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 286 2 22 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 286 2 21 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 286 (accept_3_3 41 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 286 2 20 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 178 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 286 2 19 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 286 2 18 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 286 (accept_3_3 35 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 286 2 17 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 178 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 286 2 16 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 286
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 31 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 286 2 15 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 286 (accept_3_3 29 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 286 2 14 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 286 2 13 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 286 2 12 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 286 (accept_3_3 23 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 286 2 11 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 286 (Polychromatic418967fa.accept_19_2_7_1_1_2808 21 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 286 2 10 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 286
  (Polychromatic418967fa.accept_25_19_3_11_1_12503 19 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 178 286 2 9 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 178 286 (accept_3_3 17 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 286 2 8 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 286 (Polychromatic418967fa.accept_25_15_3_11_1_12481 15 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 286 2 7 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 286 2 6 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 286 (accept_3_3 11 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 286 2 5 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 178 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 286 2 4 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 286
  (Polychromatic418967fa.accept_17_7_8_14_1_6720 7 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 286 2 3 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 286 (accept_3_3 5 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  286 2 2 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 178 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 286 2 1 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 286 (Polychromatic418967fa.accept_21_1_10_13_1_5623 1 178 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 177 286 (Eq.refl Bool.true) (allA_succ_of_accept 109 177 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  109 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 177 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 108 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 177 286 (accept_3_3 107 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 177 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 106 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 177 286 (Polychromatic418967fa.accept_19_10_6_1_1_6828 105 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 177 286 (accept_3_3 104 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 177
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 177 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 102 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 177 286 (accept_3_3 101 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 177 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 100 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 177 286 (accept_3_3 98 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 177 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 177 286
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 96 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 177 286 (accept_3_3 95 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 177 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 94 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 177 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 177 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 177 286 (accept_3_3 92 177 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 177 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 90 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 177 286 (accept_3_3 89 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 177 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 177 286 (accept_3_3 86 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 177 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 177 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 177 286 (accept_3_3 83 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 177 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 177 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 177 286 (accept_3_3 80 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 177 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 177 286 (accept_3_3 77 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 177 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 177 286 (accept_3_3 74 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 177 286
  (Polychromatic418967fa.accept_17_4_7_14_1_10583 72 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 177 286 (accept_3_3 71 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 177 286 (Polychromatic418967fa.accept_21_7_9_13_1_5612 70 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 177 286 (Polychromatic418967fa.accept_20_9_17_6_1_6098 69 177
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 177 286 (accept_3_3 68 177
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 177 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 177 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 177 286 (accept_3_3 65 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 177 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 177 286 (accept_3_3 62
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 61 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 177 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 177 286 (accept_3_3 59 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 177 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 57
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 177 286 (accept_3_3 56
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 177 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 286 (accept_3_3 53 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 177 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 286 (accept_3_3 50
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 49 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 177 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 286 (accept_3_3 47 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 177 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 286 (accept_3_3 44
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 177 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 286 (accept_3_3 41 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 177 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 286 (accept_3_3 38
  177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 177 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 286 (accept_3_3 35 177 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 177 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 286
  (Polychromatic418967fa.accept_10_3_7_6_1_659 33 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 177 286 (accept_3_3 32 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 177 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 286 (accept_3_3 29 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 177 286 (accept_3_3 26 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 177 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 177 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 286 (accept_3_3 23 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 177 286 (accept_3_3 20 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 177 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 286 (accept_3_3 17 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 286 (Polychromatic418967fa.accept_20_16_17_6_1_7799 16 177 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 177 286 (accept_3_3 14 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 177 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 177 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 286 (accept_3_3 11 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 286
  (Polychromatic418967fa.accept_18_9_15_16_1_8759 9 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 177 286 (accept_3_3 8 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  177 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 177 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 286 (accept_3_3 5 177 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 177 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 286 (accept_3_3 2 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 176 286 (Eq.refl Bool.true) (allA_of_3_1 111 176 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 112 175 286 (Eq.refl Bool.true) (allA_succ_of_accept 111 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 175 286 (accept_3_3 110 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 175 286 (Polychromatic418967fa.accept_29_21_1_25_1_17589 108 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 175 286 (accept_3_3 107 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 175 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 106 175
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 175 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 175 286 (accept_3_3 104 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 175 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 103 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 175 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 102 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 175 286 (accept_3_3 101 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 175 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 175 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 175 286 (accept_3_3 98 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 175 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 175 286 (accept_3_3 95 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 175 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 94 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 175 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 175 286 (accept_3_3 92 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 175 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 175 286 (Polychromatic418967fa.accept_16_10_15_14_1_1086 90 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 175 286 (accept_3_3 89 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 175 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 175
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 175 286 (accept_3_3 86 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 175 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 175 286 (accept_3_3 83 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 175 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 175 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 175 286 (accept_3_3 80 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 175 286 (Polychromatic418967fa.accept_10_9_5_6_1_691 79 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 175 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 175 286 (accept_3_3 77 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 175 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 175 286 (accept_3_3 74 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 175 286 (Polychromatic418967fa.accept_19_15_4_1_1_4060 72 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 175 286 (accept_3_3 71 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 175 286 (Polychromatic418967fa.accept_17_2_5_14_1_2068 70 175
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 175 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 175 286 (accept_3_3 68 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 175 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 175 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 175 286 (accept_3_3 65 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 175 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 175 286 (accept_3_3 62 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 175 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 175 286 (accept_3_3 59 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 175 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 58 175 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 175 286 (accept_3_3 56 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 175 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 175 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 286 (accept_3_3 53 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 175 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 175
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 175 286 (accept_3_3 50 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 286 (accept_3_3 47 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 175 286 (accept_3_3 44 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 175 286 (Polychromatic418967fa.accept_14_1_7_6_1_3604 43 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 175 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 286 (accept_3_3 41 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 175 286 (accept_3_3 38 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 175 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 286 (accept_3_3 35 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 175 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 175
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 286 (accept_3_3 32 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 286 (accept_3_3 29 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 286 (accept_3_3 26 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 286 (accept_3_3 23 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 286 (accept_3_3 20 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 286 (Polychromatic418967fa.accept_21_18_7_13_1_8801 18 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 286 (accept_3_3 17 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 175
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 286 (accept_3_3 14 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 286 (accept_3_3 11 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 286 (accept_3_3 8 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 286 (accept_3_3 5 175 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 175 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 286 (accept_3_3 2 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 175 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 174 286 (Eq.refl Bool.true) (allA_succ_of_gcd 112 174 286 2 56 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 174 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 111 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 174 286 2 55 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 174 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 109 174 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 174 286 2 54 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 174 286 (accept_3_3 107 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 174 286 2 53 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 174 286 (Polychromatic418967fa.accept_9_6_3_7_1_580
  105 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 174 286 2 52 87 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 174 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 103 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 174 286 2 51 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 174 286 (accept_3_3 101 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 174 286 2 50 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 174 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 99 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 174 286 2 49 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 174 286
  (Polychromatic418967fa.accept_15_7_9_1_1_473 97 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 174 286 2 48 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 174 286 (accept_3_3 95 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 174 286 2 47 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 174 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 93 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 174 286 2 46 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 174 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 174 286 2 45 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 174 286 (accept_3_3 89 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 174 286 2 44 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 174 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 174 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 174 286 2 43 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 174 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 85 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 174 286 2 42 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 174 286 (accept_3_3 83 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 174 286 2 41 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 174 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 81 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 174 286 2 40 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 174 286
  (Polychromatic418967fa.accept_20_19_14_6_1_4726 79 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 174 286 2 39 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 174 286 (accept_3_3 77 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 174 286 2 38 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 174 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 75 174 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 174 286 2 37 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 174 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 286 2 36 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 286 (accept_3_3 71 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 174 286 2 35 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 174 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 174 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 174 286 2 34 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 174 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 286 2 33 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 286 (accept_3_3 65 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 174 286 2 32 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 174 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 174 286 2 31 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 286
  (Polychromatic418967fa.accept_19_4_3_1_1_17563 61 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 286 2 30 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 286 (accept_3_3 59 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 174 286 2 29 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 174 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 174 286 2 28 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 286 2 27 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 286 (accept_3_3 53 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 174 286 2 26 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 174 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 174 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 174 286 2 25 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 286 2 24 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 286 (accept_3_3 47 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 174 286 2 23 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 174 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 174 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 174 286 2 22 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 286
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 43 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 286 2 21 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 286 (accept_3_3 41 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 174 286 2 20 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 174 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 174 286 2 19 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 286 2 18 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 286 (accept_3_3 35 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 286 2 17 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 174 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 174 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 174 286 2 16 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 286 2 15 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 286 (accept_3_3 29 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 174 286 2 14 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 174 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 174 286 2 13 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 286 2 12 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 286 (accept_3_3 23 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 174 286 2 11 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 174 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 174 286 2 10 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 286 2 9 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 286 (accept_3_3 17 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 174 286 2 8 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 174 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 174 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 286 2 7 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 286 2 6 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 286 (accept_3_3 11 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 286 2 5 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 174 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 174 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 286 2 4 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 286
  (Polychromatic418967fa.accept_15_7_9_1_1_473 7 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 286 2 3 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 286 (accept_3_3 5 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174
  286 2 2 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  174 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 174 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 174 286 2 1 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 174 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 174 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 173 286 (Eq.refl Bool.true) (allA_of_3_1 114 173 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 115 172 286 (Eq.refl Bool.true) (allA_succ_of_gcd 114 172 286 2 57 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 172 286 (accept_3_3 113 172 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 172 286 2 56 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 172 286 (Polychromatic418967fa.accept_9_3_1_7_1_97
  111 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 172 286 2 55 86 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 172 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 109 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 172 286 2 54 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 172 286 (accept_3_3 107 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 172 286 2 53 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 172 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 105 172 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 172 286 2 52 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 172 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 103 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 172 286 2 51 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 172 286 (accept_3_3 101 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 172 286 2 50 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 172 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 99 172 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 172 286 2 49 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 172 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 97 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 172 286 2 48 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 172 286 (accept_3_3 95 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 172 286 2 47 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 172 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 172 286 2 46 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 172 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 91 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 172 286 2 45 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 172 286 (accept_3_3 89 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 172 286 2 44 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 172 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 172 286 2 43 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 172 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 85 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 172 286 2 42 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 172 286 (accept_3_3 83 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 172 286 2 41 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 172 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 172 286 2 40 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 172 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 79 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 172 286 2 39 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 172 286 (accept_3_3 77 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 172 286 2 38 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 172 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 172 286 2 37 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 172 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 172 286 2 36 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 172 286 (accept_3_3 71 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 172 286 2 35 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 172 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 172 286 2 34 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 172 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 172 286 2 33 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 172 286 (accept_3_3 65 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 172 286 2 32 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 172 286 (Polychromatic418967fa.accept_23_17_11_10_1_11257 63 172 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 172 286 2 31 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 172 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 172 286 2 30 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 172 286 (accept_3_3 59 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 172 286 2 29 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 172 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 172 286 2 28 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 172 286 2 27 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 172 286 (accept_3_3 53 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 172 286 2 26 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 172 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 286 2 25 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 172 286 2 24 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 172 286 (accept_3_3 47 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 286 2 23 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 286 2 22 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 172 286 2 21 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 172 286 (accept_3_3 41 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 286 2 20 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 286 2 19 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 286 2 18 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 172 286 (accept_3_3 35 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 172 286 2 17 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 172 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 286 2 16 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 172 286 2 15 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 172 286 (accept_3_3 29 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 172 286 2 14 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 172 286 (Polychromatic418967fa.accept_20_7_12_6_1_2164 27 172 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 172 286 2 13 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 172 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 172 286 2 12 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 172 286 (accept_3_3 23 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 172 286 2 11 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 172 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 286 2 10 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 286 2 9 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 286 (accept_3_3 17 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 286 2 8 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 172 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 286 2 7 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 286 2 6 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 172 286 (accept_3_3 11 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 286 2 5 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 172 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 286 2 4 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 172 286 2 3 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 286 (accept_3_3 5 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  286 2 2 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 172 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 286 2 1 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 172 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 172 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 171 286 (Eq.refl Bool.true) (allA_succ_of_accept 115 171 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  115 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 171 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 114 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 171 286 (accept_3_3 113 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 171 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 112 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 171 286 (Polychromatic418967fa.accept_21_6_3_13_1_2742 111 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 171 286 (accept_3_3 110 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 171 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 171 286
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 108 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 171 286 (accept_3_3 107 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 171 286 (Polychromatic418967fa.accept_17_4_1_14_1_4296 106 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3
  105 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 171 286 (accept_3_3
  104 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 171 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 103 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 171 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 171 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 171 286 (accept_3_3 101 171 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 171 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 100 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 171 286 (Polychromatic418967fa.accept_15_9_6_1_1_493
  99 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 171 286 (accept_3_3 98
  171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 171 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 97 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 171 286 (Polychromatic418967fa.accept_20_16_11_6_1_10684 96 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 171 286 (accept_3_3 95 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 171 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 94 171 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 171 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 171 286 (accept_3_3 92 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 171 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 171 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 90 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 171 286 (accept_3_3 89 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 171 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 88 171 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 171 286
  (Polychromatic418967fa.accept_10_7_1_6_1_673 87 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 171 286 (accept_3_3 86 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 171 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 84 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 171 286 (accept_3_3 83 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 171 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 82 171
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 171 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 171 286 (accept_3_3 80 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 171 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 171 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 78 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 171 286 (accept_3_3 77 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 171 286 (Polychromatic418967fa.accept_20_16_11_6_1_10684 76
  171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 171 286
  (Polychromatic418967fa.accept_10_5_1_6_1_672 75 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 171 286 (accept_3_3 74 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 171 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 171 286 (accept_3_3 71 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 286 (Polychromatic418967fa.accept_15_10_6_1_1_3707 70 171 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 171 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 171 286 (accept_3_3 68 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 171 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 171 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 66 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 171 286 (accept_3_3 65 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 286 (Polychromatic418967fa.accept_17_13_1_14_1_1149 64 171
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 171 286
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 171 286 (accept_3_3 62 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 171 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 286 (accept_3_3 59 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 171 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 171 286 (accept_3_3 56 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 171 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 171 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 286 (accept_3_3 53 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 171
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 171 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 171 286 (accept_3_3 50 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 171 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 286 (accept_3_3 47 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 171 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 171 286 (accept_3_3 44 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 171 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 171 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 286 (accept_3_3 41 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 286 (Polychromatic418967fa.accept_15_10_6_1_1_3707 40 171
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 171 286 (accept_3_3 38 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 171 286 (Polychromatic418967fa.accept_20_16_11_6_1_10684 36 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 286 (accept_3_3 35 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 286 (Polychromatic418967fa.accept_20_14_11_6_1_6264 34 171
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 171 286 (accept_3_3 32 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 171 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 171 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 286 (accept_3_3 29 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 286 (Polychromatic418967fa.accept_27_1_9_16_1_10028 28 171 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 286
  (Polychromatic418967fa.accept_10_7_1_6_1_673 27 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 171 286 (accept_3_3 26 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 171 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 286 (accept_3_3 23 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 171
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 171 286 (accept_3_3 20 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 171 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 171 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 286 (accept_3_3 17 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 286
  (Polychromatic418967fa.accept_10_5_1_6_1_672 15 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 286 (accept_3_3 14 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 286 (accept_3_3 11 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 171
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 286 (accept_3_3 8 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 286 (accept_3_3 5 171 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 171 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 286
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 286 (accept_3_3 2 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 170 286 (Eq.refl Bool.true) (allA_of_3_1 117 170 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 118 169 286 (Eq.refl Bool.true) (allA_succ_of_gcd 117 169 286 13 9 13 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 169 286 (accept_3_3 116 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 169
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 169 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 114 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 169 286 (accept_3_3 113 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 169 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 112 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 169 286 (accept_3_3 110 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 169 286 (Polychromatic418967fa.accept_18_1_7_16_1_1342 109
  169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 169 286
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 108 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 169 286 (accept_3_3 107 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 169 286 (Polychromatic418967fa.accept_25_6_19_11_1_6969 106 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 169 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 105 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 169 286 13 8 13 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 169 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 103 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 169 286 (Polychromatic418967fa.accept_15_12_4_1_1_3746 102 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 169 286 (accept_3_3 101 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 169 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 100 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 169 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 169 286 (accept_3_3 98 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 169 286 (Polychromatic418967fa.accept_20_17_9_6_1_6219 97 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 169 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 169 286 (accept_3_3 95 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 169 286 (Polychromatic418967fa.accept_18_4_7_16_1_2307 94 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 169 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 169 286 (accept_3_3 92 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91
  169 286 13 7 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 90 169 286 (Polychromatic418967fa.accept_19_14_17_1_1_2788 90 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 169 286 (accept_3_3 89 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 169 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 88 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 169 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 169 286 (accept_3_3 86 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 169 286 (Polychromatic418967fa.accept_10_5_9_6_1_697 85 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 169 286 (Polychromatic418967fa.accept_16_4_9_14_1_3883 84 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 169 286 (accept_3_3 83 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 169 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 169 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 169 286 (accept_3_3 80 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 169 286 13 6 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 169 286 (accept_3_3 77 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 169 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 169 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 169 286 (accept_3_3 74 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 169 286 (Polychromatic418967fa.accept_10_3_9_6_1_94
  73 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 169 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 169 286 (accept_3_3 71 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 169 286 (Polychromatic418967fa.accept_17_2_16_14_1_2116 70 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 169 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 169 286 (accept_3_3 68 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 169 286
  (Polychromatic418967fa.accept_17_15_16_14_1_4291 66 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 169 286 13 5 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 169 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 169 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 169 286 (accept_3_3 62 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 169 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 169 286 (Polychromatic418967fa.accept_19_3_17_1_1_781 60 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 169 286 (accept_3_3 59 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 286 (accept_3_3 56 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 286 (accept_3_3 53 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 169 286 13 4 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 286 (accept_3_3 50 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 286 (Polychromatic418967fa.accept_14_7_1_6_1_3514
  49 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 286
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 48 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 286 (accept_3_3 47 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 286 (Polychromatic418967fa.accept_21_4_1_13_1_8751 46 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 286 (accept_3_3 44 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 286
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 286 (accept_3_3 41 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 169 286 13 3 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 169 286 (accept_3_3 38 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 169 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 169 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 286 (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 169
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 286 (accept_3_3 35 169
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 286
  (Polychromatic418967fa.accept_19_15_17_1_1_8225 34 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 286 (accept_3_3 32 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 286 (accept_3_3 29 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 169 286 13 2 13 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 169 286
  (Polychromatic418967fa.accept_10_5_9_6_1_697 25 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 169 286 (Polychromatic418967fa.accept_27_24_7_16_1_17588 24 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 286 (accept_3_3 23 169 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 286 (Polychromatic418967fa.accept_18_4_7_16_1_2307 22 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 286 (accept_3_3 20 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 286 (accept_3_3 17 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 286 (accept_3_3 14 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13
  169 286 13 1 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 169 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 169 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 286 (accept_3_3 11 169 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 169 286 (Polychromatic418967fa.accept_19_10_17_1_1_4010 10 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 286 (accept_3_3 8 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 286 (Polychromatic418967fa.accept_24_6_1_22_1_14202 6 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 286 (accept_3_3 5 169 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 169 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 286 (accept_3_3 2 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 286 (Polychromatic418967fa.accept_18_1_7_16_1_1342 1 169 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 168 286 (Eq.refl Bool.true) (allA_succ_of_gcd 118 168 286 2 59 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 168 286
  (Polychromatic418967fa.accept_19_3_16_1_1_8246 117 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 168 286 2 58 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 168 286 (Polychromatic418967fa.accept_31_22_13_7_1_17587 115 168 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 168 286 2 57 84 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 168 286 (accept_3_3
  113 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 168 286 2 56 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 168 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 111 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 168 286 2 55 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 168 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 109 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 168 286 2 54 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 168 286 (accept_3_3 107 168 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 168 286 2 53 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 168 286
  (Polychromatic418967fa.accept_17_3_15_14_1_4219 105 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 168 286 2 52 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 168 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 103 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 168 286 2 51 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 168 286 (accept_3_3 101 168 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 168 286 2 50 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 168 286
  (Polychromatic418967fa.accept_19_4_16_1_1_8332 99 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 168 286 2 49 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 168 286 (Polychromatic418967fa.accept_17_12_15_14_1_6746 97 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 168 286 2 48 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 168 286 (accept_3_3 95 168 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 168 286 2 47 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 168 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 93 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 168 286 2 46 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 168 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 168 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 168 286 2 45 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 168 286 (accept_3_3 89 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 168 286 2 44 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 168 286
  (Polychromatic418967fa.accept_18_15_6_16_1_4730 87 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 168 286 2 43 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 168 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 85 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 168 286 2 42 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 168 286 (accept_3_3 83 168 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 168 286 2 41 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 168 286
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 81 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 168 286 2 40 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 168 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 79 168 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 168 286 2 39 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 168 286 (accept_3_3 77 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 168 286 2 38 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 168 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 75
  168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 168 286 2 37 84 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 168 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 168 286 2 36 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 168 286 (accept_3_3 71 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 168 286 2 35 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 168 286 (Polychromatic418967fa.accept_18_15_6_16_1_4730 69 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 168 286 2 34 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 168 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 286 2 33 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 286 (accept_3_3 65 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 168 286 2 32 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 168 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 168 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 168 286 2 31 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 286
  (Polychromatic418967fa.accept_19_4_16_1_1_8332 61 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 286 2 30 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 286 (accept_3_3 59 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 168 286 2 29 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 168 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 168 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 168 286 2 28 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 286 2 27 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 286 (accept_3_3 53 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 168 286 2 26 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 168 286 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 168 286 2 25 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 286 2 24 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 286 (accept_3_3 47 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 168 286 2 23 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 168 286 (Polychromatic418967fa.accept_25_20_18_11_1_17586 45 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 168 286 2 22 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 286 2 21 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 286 (accept_3_3 41 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 286 2 20 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 168 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 168 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 286 2 19 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 286 2 18 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 168 286 (accept_3_3 35 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 168 286 2 17 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 168 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 168 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 168 286 2 16 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 286 2 15 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 286 (accept_3_3 29 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 286 2 14 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 168 286 (Polychromatic418967fa.accept_19_8_16_1_1_11051 27 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 286 2 13 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 286
  (Polychromatic418967fa.accept_31_25_13_7_1_17585 25 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 168 286 2 12 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 168 286 (accept_3_3 23 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 168 286 2 11 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 168 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 168 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 168 286 2 10 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 286 2 9 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 286 (accept_3_3 17 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 286 2 8 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 168 286 (Polychromatic418967fa.accept_18_15_6_16_1_4730 15 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 286 2 7 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 286 2 6 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 286 (accept_3_3 11 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 286 2 5 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 168 286 (Polychromatic418967fa.accept_27_9_6_16_1_17584 9 168 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 286 2 4 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 286
  (Polychromatic418967fa.accept_25_7_18_11_1_17583 7 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 168 286 2 3 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 168 286 (accept_3_3 5 168 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 168 286 2 2 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 168 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 168 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 286 2 1 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  168 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 167 286 (Eq.refl Bool.true) (allA_of_3_1 120 167 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 121 166 286 (Eq.refl Bool.true) (allA_succ_of_gcd 120 166 286 2 60 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 166 286 (accept_3_3 119 166 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 166 286 2 59 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 166 286
  (Polychromatic418967fa.accept_29_1_21_25_1_17582 117 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 166 286 2 58 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 166 286 (Polychromatic418967fa.accept_18_7_4_16_1_2299 115 166 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 166 286 2 57 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 166 286 (accept_3_3
  113 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 166 286 2 56 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 166 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 111 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 166 286 2 55 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 166 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 109 166 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 166 286 2 54 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 166 286 (accept_3_3 107 166 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 166 286 2 53 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 166 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 105 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 166 286 2 52 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 166 286 (Polychromatic418967fa.accept_17_1_13_14_1_478 103 166 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 166 286 2 51 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 166 286 (accept_3_3 101 166 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 166 286 2 50 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 166 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 166 286 2 49 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 166 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 97 166 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 166 286 2 48 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 166 286 (accept_3_3 95 166 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 166 286 2 47 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 166 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 93 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 166 286 2 46 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 166 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 166 286 2 45 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 166 286 (accept_3_3 89 166 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 166 286 2 44 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 166 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 87
  166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 166 286 2 43 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 166 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 85 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 166 286 2 42 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 166 286 (accept_3_3 83 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 166 286 2 41 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 166 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 166 286 2 40 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 166 286
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 79 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 166 286 2 39 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 166 286 (accept_3_3 77 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 166 286 2 38 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 166 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 166 286 2 37 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 166 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 166 286 2 36 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 166 286 (accept_3_3 71 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 166 286 2 35 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 166 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 166 286 2 34 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 166 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 166 286 2 33 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 166 286 (accept_3_3 65 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 166 286 2 32 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 286 (Polychromatic418967fa.accept_19_6_14_1_1_2752 63 166 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 166 286 2 31 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 166 286
  (Polychromatic418967fa.accept_17_10_13_14_1_3094 61 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 166 286 2 30 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 166 286 (accept_3_3 59 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 166 286 2 29 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 166 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 286 2 28 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 286 2 27 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 286 (accept_3_3 53 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 286 2 26 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 286 2 25 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 286
  (Polychromatic418967fa.accept_21_7_19_13_1_7164 49 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 166 286 2 24 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 166 286 (accept_3_3 47 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 286 2 23 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 286 (Polychromatic418967fa.accept_23_22_5_10_1_12911 45 166 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 286 2 22 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 286 2 21 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 286 (accept_3_3 41 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 286 2 20 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 286 2 19 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 286 2 18 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 286 (accept_3_3 35 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 286 2 17 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 286 2 16 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 286
  (Polychromatic418967fa.accept_28_3_26_6_1_17581 31 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 166 286 2 15 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 166 286 (accept_3_3 29 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 286 2 14 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 166 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 286 2 13 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 286 2 12 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 286 (accept_3_3 23 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 286 2 11 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 286 2 10 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 286 2 9 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 286 (accept_3_3 17 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 286 2 8 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 286 2 7 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 286
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 166 286 2 6 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 166 286 (accept_3_3 11 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 286 2 5 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 286 (Polychromatic418967fa.accept_19_9_14_1_1_6792 9 166 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 286 2 4 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 286
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 286 2 3 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 286 (accept_3_3 5 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  286 2 2 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 166 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 286 2 1 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 166 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 165 286 (Eq.refl Bool.true) (allA_succ_of_gcd 121 165 286 11 11 15 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 120 165 286
  (Polychromatic418967fa.accept_21_15_18_13_1_8747 120 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 165 286 (accept_3_3 119 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 165 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 118 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 165 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 117 165
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 165 286 (accept_3_3 116 165
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 165 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 115 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 165 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 114 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 165 286 (accept_3_3 113 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 165 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 112 165 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 165 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 165 286 11 10 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 165 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 165 286 (Polychromatic418967fa.accept_7_3_4_6_1_329
  108 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 165 286 (accept_3_3
  107 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 165 286
  (Polychromatic418967fa.accept_16_10_5_14_1_6173 106 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 165 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 105 165 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 165 286 (accept_3_3 104 165 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 165
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 165 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 102 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 165 286 (accept_3_3 101 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 165 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 100 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 165 286 11 9 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 165 286 (accept_3_3 98 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 165 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 165 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 165 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 165 286 (accept_3_3 95 165 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 165 286 (Polychromatic418967fa.accept_7_3_4_6_1_329
  94 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 165 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 93 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 165 286 (accept_3_3 92 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 165 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 90 165 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 165 286 (accept_3_3 89 165 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 165 286 11 8 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 87
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 165 286 (accept_3_3 86
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 165 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 85 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 165 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 84 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 165 286 (accept_3_3 83 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 165 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 165 286 (Polychromatic418967fa.accept_10_1_5_6_1_649
  81 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 165 286 (accept_3_3 80
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 165 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 165 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 78 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 165 286 11 7 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 165 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 76
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 165 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 165 286 (accept_3_3 74 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 165 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 165 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 286 (accept_3_3 71 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 286 (Polychromatic418967fa.accept_20_10_5_6_1_12032 70 165 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 165 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 165 286 (accept_3_3 68 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 165 286 11 6 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 165 286 (accept_3_3 65 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 165 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 286 (accept_3_3 62 165 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 165 286 (accept_3_3 59 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 165 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 165 286 (Polychromatic418967fa.accept_16_9_5_14_1_6126 57 165 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 286 (accept_3_3 56 165 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 165 286 11 5 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 165 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 54
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 286 (accept_3_3 53
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 52 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 286 (accept_3_3 50 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 165 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 286
  (Polychromatic418967fa.accept_19_10_13_1_1_8264 48 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 165 286 (accept_3_3 47 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 165 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 165 286 11 4 15 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 165 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 165 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 286 (accept_3_3 41 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 165 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 286 (accept_3_3 38
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 165 286 (Polychromatic418967fa.accept_21_15_18_13_1_8747 36 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 286 (accept_3_3 35 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 165 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 286 11 3 15 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 286 (accept_3_3 32 165 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 165 286 (accept_3_3 29 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 165 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 286 (accept_3_3 26 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 165 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 286 (accept_3_3 23 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  165 286 11 2 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 165 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 286 (accept_3_3 20 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 286 (Polychromatic418967fa.accept_12_6_9_10_1_565
  18 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 286 (accept_3_3 17
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 286 (accept_3_3 14 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 165 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 286 (Polychromatic418967fa.accept_7_5_4_6_1_167
  12 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 165 286 11 1 15 26
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 165 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 10 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 165 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 286 (accept_3_3 8 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6
  165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 286 (accept_3_3 5 165
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 4 165 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 165 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 286 (accept_3_3 2 165 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 165 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 164 286 (Eq.refl Bool.true) (allA_of_3_1 123 164 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 124 163 286 (Eq.refl Bool.true) (allA_succ_of_accept 123 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 163 286 (accept_3_3 122 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 163 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 120 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 163 286 (accept_3_3 119 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 163 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 118 163
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 117 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 163 286 (accept_3_3 116 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 163 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 115 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 163 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 114 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 163 286 (accept_3_3 113 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 163 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 112 163
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 163 286 (accept_3_3 110 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 163 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 108 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 163 286 (accept_3_3 107 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 163 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 106 163
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 163 286 (accept_3_3 104 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 163 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 103 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 163 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 102 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 163 286 (accept_3_3 101 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 163 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 100 163
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 163 286 (accept_3_3 98 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 163 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 163 286 (accept_3_3 95 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 163 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 94 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 163 286 (accept_3_3 92 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 163 286 (Polychromatic418967fa.accept_16_11_3_14_1_5043 91 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 163 286 (Polychromatic418967fa.accept_17_5_10_14_1_2083 90 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 163 286 (accept_3_3 89 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 163 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 163 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 163 286 (accept_3_3 86 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 163 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 163 286 (accept_3_3 83 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 163 286 (Polychromatic418967fa.accept_18_10_1_16_1_579 82 163 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 163 286 (accept_3_3 80 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 163 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 79 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 163 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 163 286 (accept_3_3 77 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 163 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 163 286 (accept_3_3 74 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 163 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 72 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 286 (accept_3_3 71 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 163
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 286 (accept_3_3 68 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 163 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 286 (accept_3_3 65 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 163 286 (accept_3_3 62 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 163 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 286 (accept_3_3 59 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 163 286 (accept_3_3 56 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 163 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 163 286 (Polychromatic418967fa.accept_23_8_2_10_1_12909 54 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 286 (accept_3_3 53 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 163 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 163 286 (accept_3_3 50 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 286 (accept_3_3 47 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 286 (accept_3_3 44 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 286 (accept_3_3 41 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 286 (accept_3_3 38 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 286 (accept_3_3 35 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 286 (Polychromatic418967fa.accept_19_15_11_1_1_12437 34 163 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 286 (accept_3_3 32 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 286 (accept_3_3 29 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 286 (accept_3_3 26 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 286 (accept_3_3 23 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 286 (accept_3_3 20 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 286 (accept_3_3 17 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 286 (accept_3_3 14 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 286 (accept_3_3 11 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 286 (accept_3_3 8 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 286 (accept_3_3 5 163 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 163 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 286 (accept_3_3 2 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 162 286 (Eq.refl Bool.true) (allA_succ_of_gcd 124 162 286 2 62 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 162 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 123 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 162 286 2 61 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 162 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 121 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 162 286 2 60 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 162 286 (accept_3_3 119 162 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 162 286 2 59 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 162 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 117 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 162 286 2 58 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 162 286 (Polychromatic418967fa.accept_25_15_12_11_1_17580 115 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 162 286 2 57 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 162 286 (accept_3_3 113 162 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 162 286 2 56 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 162 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 111 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 162 286 2 55 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 162 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 109 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 162 286 2 54 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 162 286 (accept_3_3 107 162 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 162 286 2 53 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 162 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 105 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 162 286 2 52 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 162 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 103 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 162 286 2 51 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 162 286 (accept_3_3 101 162 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 162 286 2 50 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 162 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 99 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 162 286 2 49 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 162 286 (Polychromatic418967fa.accept_17_12_9_14_1_4283 97 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 162 286 2 48 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 162 286 (accept_3_3 95 162 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 162 286 2 47 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 162 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 162 286 2 46 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 162 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 91 162 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 162 286 2 45 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 162 286 (accept_3_3 89 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 162 286 2 44 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 162 286 (Polychromatic418967fa.accept_12_3_6_10_1_576
  87 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 162 286 2 43 81 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 162 286
  (Polychromatic418967fa.accept_19_9_10_1_1_8329 85 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 162 286 2 42 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 162 286 (accept_3_3 83 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 162 286 2 41 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 162 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 162 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 162 286 2 40 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 162 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 286 2 39 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 286 (accept_3_3 77 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 162 286 2 38 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 162 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 162 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 162 286 2 37 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 162 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 73 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 162 286 2 36 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 162 286 (accept_3_3 71 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 162 286 2 35 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 162 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 162 286 2 34 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 286
  (Polychromatic418967fa.accept_29_9_17_25_1_17579 67 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 162 286 2 33 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 162 286 (accept_3_3 65 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 162 286 2 32 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 162 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 162 286 2 31 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 286 2 30 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 286 (accept_3_3 59 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 162 286 2 29 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 162 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 162 286 2 28 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 286
  (Polychromatic418967fa.accept_17_4_9_14_1_5406 55 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 286 2 27 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 286 (accept_3_3 53 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 162 286 2 26 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 162 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 162 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 162 286 2 25 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 49 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 286 2 24 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 286 (accept_3_3 47 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 162 286 2 23 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 162 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 162 286 2 22 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 162 286 2 21 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 162 286 (accept_3_3 41 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 162 286 2 20 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 162 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 162 286 2 19 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 286 2 18 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 286 (accept_3_3 35 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 162 286 2 17 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 162 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 162 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 162 286 2 16 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 286 2 15 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 286 (accept_3_3 29 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 286 2 14 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 162 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 286 2 13 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 286
  (Polychromatic418967fa.accept_19_6_10_1_1_5394 25 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 286 2 12 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 286 (accept_3_3 23 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 286 2 11 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 162 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 162 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 286 2 10 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 286 2 9 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 286 (accept_3_3 17 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 286 2 8 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 162 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 286 2 7 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 286 2 6 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 286 (accept_3_3 11 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 286 2 5 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 162 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 162 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 286 2 4 81 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 286 2 3 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 286 (accept_3_3 5 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162
  286 2 2 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  162 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 162 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 162 286 2 1 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 162 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 162 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 126 161 286 (Eq.refl Bool.true) (allA_of_3_1 126 161 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 127 160 286 (Eq.refl Bool.true) (allA_succ_of_gcd 126 160 286 2 63 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 160 286 (accept_3_3 125 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 160 286 2 62 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 160 286
  (Polychromatic418967fa.accept_17_4_7_14_1_10583 123 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 122 160 286 2 61 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 121 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 121 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 160 286 2 60 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 160 286 (accept_3_3
  119 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 160 286 2 59 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 160 286
  (Polychromatic418967fa.accept_24_21_16_22_1_14198 117 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 160 286 2 58 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 115 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 160 286 2 57 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 160 286 (accept_3_3
  113 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 160 286 2 56 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 160 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 111 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 160 286 2 55 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 109 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 160 286 2 54 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 160 286 (accept_3_3
  107 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 160 286 2 53 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 160 286
  (Polychromatic418967fa.accept_23_13_22_10_1_9668 105 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 160 286 2 52 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 103 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 160 286 2 51 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 160 286 (accept_3_3
  101 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 160 286 2 50 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 160 286
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 99 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 160 286 2 49 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 97 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 160 286 2 48 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 160 286 (accept_3_3 95 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 160 286 2 47 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 160 286
  (Polychromatic418967fa.accept_17_8_7_14_1_11730 93 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 160 286 2 46 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 91 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 160 286 2 45 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 160 286 (accept_3_3 89 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 160 286 2 44 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 160 286
  (Polychromatic418967fa.accept_19_11_8_1_1_801 87 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 160 286 2 43 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 85 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 160 286 2 42 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 160 286 (accept_3_3 83 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 160 286 2 41 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 160 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 160 286 2 40 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 79 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 160 286 2 39 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 160 286 (accept_3_3 77 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 160 286 2 38 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 160 286
  (Polychromatic418967fa.accept_19_18_8_1_1_11071 75 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 160 286 2 37 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 73 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 160 286 2 36 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 160 286 (accept_3_3 71 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 160 286 2 35 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 160 286
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 69 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 160 286 2 34 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 67 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 160 286 2 33 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 160 286 (accept_3_3 65 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 160 286 2 32 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 160 286
  (Polychromatic418967fa.accept_27_9_25_16_1_8138 63 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 160 286 2 31 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 61 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 160 286 2 30 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 160 286 (accept_3_3 59 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 160 286 2 29 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 160 286
  (Polychromatic418967fa.accept_17_6_7_14_1_6704 57 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 160 286 2 28 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 55 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 160 286 2 27 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 160 286 (accept_3_3 53 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 160 286 2 26 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 160 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 51 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 160 286 2 25 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 160 286 2 24 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 160 286 (accept_3_3 47 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 160 286 2 23 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 160 286
  (Polychromatic418967fa.accept_19_7_8_1_1_4028 45 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 160 286 2 22 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 160 286 2 21 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 160 286 (accept_3_3 41 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 160 286 2 20 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 160 286
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 39 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 160 286 2 19 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 160 286 2 18 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 160 286 (accept_3_3 35 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 160 286 2 17 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 160 286
  (Polychromatic418967fa.accept_24_9_16_22_1_14228 33 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 160 286 2 16 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 286 2 15 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 286 (accept_3_3 29 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 286 2 14 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 286
  (Polychromatic418967fa.accept_17_10_7_14_1_4244 27 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 160 286 2 13 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 160 286 2 12 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 286 (accept_3_3 23 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 286 2 11 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 160 286 2 10 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 286 2 9 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 286 (accept_3_3 17 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 286 2 8 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 286
  (Polychromatic418967fa.accept_19_15_8_1_1_6794 15 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 160 286 2 7 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 160 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 160 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 286 2 6 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 286 (accept_3_3 11 160 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 286 2 5 80 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 286
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 160 286 2 4 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 160 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 160 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 286 2 3 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 286 (accept_3_3 5 160 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 286 2 2 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 286 (Polychromatic418967fa.accept_27_3_25_16_1_17539 3 160
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 286 2 1 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 160 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 159 286 (Eq.refl Bool.true) (allA_succ_of_accept 127 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  127 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 159 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 126 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 159 286 (accept_3_3 125 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 159 286 (Polychromatic418967fa.accept_19_10_7_1_1_1685 124 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 123 159 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 123 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 159 286 (accept_3_3 122 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 159 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 120 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 159 286 (accept_3_3 119 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 159 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 118 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 159 286 (accept_3_3 116 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 115 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 159 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 114 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 159 286 (accept_3_3 113 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 159 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 112 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 159 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 111 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 159 286 (accept_3_3 110 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 159 286
  (Polychromatic418967fa.accept_19_13_7_1_1_5379 108 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 159 286 (accept_3_3 107 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 159 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 106 159 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 159 286 (accept_3_3 104 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  103 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 159 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 102 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 159 286 (accept_3_3 101 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 159 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 100 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 159 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 159 286 (accept_3_3 98 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 159 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 96 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 159 286 (accept_3_3 95 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 159 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 94 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 159 286 (accept_3_3 92 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 159 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 90 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 159 286 (accept_3_3 89 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 159 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 159 286 (Polychromatic418967fa.accept_16_7_15_14_1_2889 87 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 159 286 (accept_3_3 86 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 159 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 159 286 (accept_3_3 83 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 159 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 159 286 (accept_3_3 80 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 159 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 159 286 (accept_3_3 77 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 159 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 159 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 286 (accept_3_3 74 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 286
  (Polychromatic418967fa.accept_21_9_12_13_1_16221 72 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 159 286 (accept_3_3 71 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 159 286 (Polychromatic418967fa.accept_15_10_9_1_1_3688 70 159 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 286 (accept_3_3 68 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67
  159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 159 286 (accept_3_3 65 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 159 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 159 286 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 286 (accept_3_3 62 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 159 286 (accept_3_3 59 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 159 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 286 (accept_3_3 56 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 159 286 (accept_3_3 53 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 159 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 286 (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 286 (accept_3_3 50 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 159 286 (accept_3_3 47 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 159 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 286 (accept_3_3 44 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 159 286 (accept_3_3 41 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 159 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 159 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 286 (accept_3_3 38 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 286 (accept_3_3 35 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 286 (Polychromatic418967fa.accept_20_14_19_6_1_12003 34 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 286 (accept_3_3 32 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 286 (accept_3_3 29 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 286 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 286 (accept_3_3 26 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 286
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 24 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 286 (accept_3_3 23 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 286 (accept_3_3 20 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 286 (accept_3_3 17 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 286 (Polychromatic418967fa.accept_33_16_27_22_1_17578 16 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 286 (accept_3_3 14 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 286 (accept_3_3 11 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 286 (accept_3_3 8 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 286 (accept_3_3 5 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 159 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 286 (accept_3_3 2 159 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 129 158 286 (Eq.refl Bool.true) (allA_of_3_1 129 158 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 130 157 286 (Eq.refl Bool.true) (allA_succ_of_accept 129 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 129 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 157 286 (accept_3_3 128 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 127 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 157 286 (Polychromatic418967fa.accept_15_6_7_1_1_93 126 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 157 286 (accept_3_3 125 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 157 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 124 157
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 123 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 157 286 (accept_3_3 122 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 157 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 121 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 157 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 120 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 157 286 (accept_3_3 119 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 157 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 118 157 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 157 286 (accept_3_3 116 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 157 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 114 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 157 286 (accept_3_3 113 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 112 157 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 112 157 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 157 286 (accept_3_3 110 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 157 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 109 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 157 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 108 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 157 286 (accept_3_3 107 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 157 286 (Polychromatic418967fa.accept_16_10_13_14_1_5042 106
  157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 157 286 (accept_3_3 104 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 157 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 157 286 (accept_3_3 101 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 157 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 100 157 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 157 286 (accept_3_3 98 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 157 286 (Polychromatic418967fa.accept_16_1_13_14_1_1064 97 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 157 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 157 286 (accept_3_3 95 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 157 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 94 157 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 157 286 (accept_3_3 92 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 157 286 (Polychromatic418967fa.accept_16_10_13_14_1_5042 90 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 157 286 (accept_3_3 89 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 157 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 88 157 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 157 286 (accept_3_3 86 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 157 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 85 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 157 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 157 286 (accept_3_3 83 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 157 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 157 286 (accept_3_3 80 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 157 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 157 286 (accept_3_3 77 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 157 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 157 286 (accept_3_3 74 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 157 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 157 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 157 286 (accept_3_3 71 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 157 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 70 157 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 157 286 (accept_3_3 68 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 157 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 286 (accept_3_3 65 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 286 (accept_3_3 62 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 286 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 157 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 286 (accept_3_3 59 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 286 (accept_3_3 56 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 286 (accept_3_3 53 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 157
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 286 (accept_3_3 50 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 286 (Polychromatic418967fa.accept_16_1_13_14_1_1064 49 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 286 (accept_3_3 47 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 286 (accept_3_3 44 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 286 (accept_3_3 41 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 286 (accept_3_3 38 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 286 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 286 (accept_3_3 35 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 286 (Polychromatic418967fa.accept_19_15_5_1_1_5360 34 157 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 286 (accept_3_3 32 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 286 (accept_3_3 29 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 286 (accept_3_3 26 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 286 (accept_3_3 23 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 286 (Polychromatic418967fa.accept_19_3_5_1_1_6811 22 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 286 (accept_3_3 20 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 286 (accept_3_3 17 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 286 (accept_3_3 14 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 286 (accept_3_3 11 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 286 (accept_3_3 8 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 286 (accept_3_3 5 157 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 157 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 286 (accept_3_3 2 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 157 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 156 286 (Eq.refl Bool.true) (allA_succ_of_gcd 130 156 286 26 5 6 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 156 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 129 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 156 286 2 64 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 156 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 127 156 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 156 286 2 63 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 156 286 (accept_3_3 125 156 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 156 286 2 62 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 156 286 (Polychromatic418967fa.accept_7_4_2_6_1_337
  123 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 156 286 2 61 78 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 156 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 121 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 156 286 2 60 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 156 286 (accept_3_3 119 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 156 286 2 59 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 117 156 286 13 9 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 116 156 286 2 58 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 156 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 115 156 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 156 286 2 57 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 156 286 (accept_3_3
  113 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 156 286 2 56 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 156 286
  (Polychromatic418967fa.accept_19_16_4_1_1_5376 111 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 156 286 2 55 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 156 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 109 156 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 156 286 2 54 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 156 286 (accept_3_3 107 156 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 156 286 2 53 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 156 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 105 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 156 286 26 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 156 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 103 156 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 156 286 2 51 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 156 286 (accept_3_3 101 156 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 156 286 2 50 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 156 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 99 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 156 286 2 49 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 156 286 (Polychromatic418967fa.accept_15_7_6_1_1_1091 97 156 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 156 286 2 48 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 156 286 (accept_3_3 95 156 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 156 286 2 47 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 156 286
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 93 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 156 286 2 46 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 91 156 286 13 7 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 156 286 2 45 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 156 286 (accept_3_3 89 156 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 156 286 2 44 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 156 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 156 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 156 286 2 43 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 156 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 156 286 2 42 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 286 (accept_3_3 83 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 156 286 2 41 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 156 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 156 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 156 286 2 40 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 156 286
  (Polychromatic418967fa.accept_17_11_3_14_1_6736 79 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 156 286 26 3 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 156 286 (accept_3_3 77 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 156 286 2 38 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 156 286 (Polychromatic418967fa.accept_21_12_9_13_1_4091 75 156 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 156 286 2 37 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 286 2 36 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 286 (accept_3_3 71 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 156 286 2 35 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 156 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 156 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 156 286 2 34 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 286 2 33 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 156 286 13 5 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 156 286 2 32 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 156
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 156 286 2 31 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 286
  (Polychromatic418967fa.accept_20_1_16_6_1_4715 61 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 286 2 30 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 286 (accept_3_3 59 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 156 286 2 29 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 156 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 156 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 156 286 2 28 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 286 2 27 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 286 (accept_3_3 53 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 286 26 2 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 156 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 156 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 156 286 2 25 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 49
  156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 156 286 2 24 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 156 286 (accept_3_3 47
  156 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 286 2 23 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 286 2 22 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 156 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 156 286 2 21 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 156 286 (accept_3_3 41 156 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 286 2 20 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 156 286 13 3 12 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 286 2 19 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 286 2 18 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 286 (accept_3_3 35 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 156 286 2 17 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 156 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 156 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 286 2 16 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 286 2 15 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 286 (accept_3_3 29 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 286 2 14 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 156 286 (Polychromatic418967fa.accept_18_9_12_16_1_7323 27 156 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 286 26 1 6 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 286 2 12 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 286 (accept_3_3 23 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 286 2 11 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 156 286 (Polychromatic418967fa.accept_20_1_16_6_1_4715 21 156 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 286 2 10 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 286 2 9 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 286 (accept_3_3 17 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 286 2 8 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 156 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 156 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 286 2 7 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 156 286 13 1 12 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 156 286 2 6 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 286 (accept_3_3 11
  156 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 286 2 5 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 286
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 286 2 4 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 286 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 156 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 286 2 3 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 286 (accept_3_3 5 156 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 286 2 2 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 286 2 1 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 156 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 132 155 286 (Eq.refl Bool.true) (allA_of_3_1 132 155 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 133 154 286 (Eq.refl Bool.true) (allA_succ_of_gcd 132 154 286 22 6 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 154 286 (accept_3_3 131 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 154 286 2 65 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 154 286 (Polychromatic418967fa.accept_9_3_1_7_1_97
  129 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 154 286 2 64 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 154 286
  (Polychromatic418967fa.accept_16_15_10_14_1_2872 127 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 126 154 286 2 63 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 125 154 286 (accept_3_3 125 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 154 286 2 62 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 154 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 123 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 154 286 2 61 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 121 154 286 11 11 14 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 120 154 286 2 60 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 154 286
  (accept_3_3 119 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 154 286 2 59 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 154 286
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 117 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 154 286 2 58 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 154 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 115 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 154 286 2 57 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 154 286 (accept_3_3 113 154 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 154 286 2 56 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 154 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 111 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 154 286 22 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 154 286 (Polychromatic418967fa.accept_16_13_10_14_1_2871 109 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 154 286 2 54 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 154 286 (accept_3_3 107 154 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 154 286 2 53 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 154 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 105 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 154 286 2 52 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 154 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 103 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 154 286 2 51 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 154 286 (accept_3_3 101 154 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 154 286 2 50 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 154 286 11 9 14 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 154 286 2 49 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 154 286
  (Polychromatic418967fa.accept_23_5_16_10_1_9686 97 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 154 286 2 48 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 154 286 (accept_3_3 95 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 154 286 2 47 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 154 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 93 154 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 154 286 2 46 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 154 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 91 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 154 286 2 45 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 154 286 (accept_3_3 89 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 154 286 22 4 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 87 154 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 87 154 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 154 286 2 43 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 154 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 85
  154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 154 286 2 42 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 154 286 (accept_3_3 83
  154 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 154 286 2 41 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 154 286
  (Polychromatic418967fa.accept_17_13_1_14_1_1149 81 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 154 286 2 40 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 154 286 (Polychromatic418967fa.accept_16_15_10_14_1_2872 79 154 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 154 286 2 39 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 154 286 11 7 14 26
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 154 286 2 38 77
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 154 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 75 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 154 286 2 37 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 154 286 (Polychromatic418967fa.accept_18_1_10_16_1_566 73 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 154 286 2 36 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 154 286 (accept_3_3 71 154 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 154 286 2 35 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 154 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 69 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 154 286 2 34 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 154 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 154 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 154 286 22 3 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 154 286 (accept_3_3 65 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 154 286 2 32 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 154 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072
  63 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 286 2 31 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 286
  (Polychromatic418967fa.accept_16_13_10_14_1_2871 61 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 154 286 2 30 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 154 286 (accept_3_3 59 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 286 2 29 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 154 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 286 2 28 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 154 286 11 5 14 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 154 286 2 27 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 154 286 (accept_3_3 53
  154 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 154 286 2 26 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 154 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 154 286 2 25 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 154 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 154 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 154 286 2 24 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 154 286 (accept_3_3 47 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 154 286 2 23 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 154 286 (Polychromatic418967fa.accept_10_5_4_6_1_319
  45 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 286 22 2 7 13
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 286
  (Polychromatic418967fa.accept_25_18_4_11_1_17577 43 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 154 286 2 21 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 154 286 (accept_3_3 41 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 286 2 20 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 154 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 286 2 19 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 286
  (Polychromatic418967fa.accept_16_5_10_14_1_5074 37 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 154 286 2 18 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 154 286 (accept_3_3 35 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 286 2 17 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 154 286 11 3 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 154 286 2 16 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 154 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 154 286 2 15 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 154 286 (accept_3_3 29
  154 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 154 286 2 14 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 154 286
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 154 286 2 13 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 154 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 154 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 154 286 2 12 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 154 286 (accept_3_3 23 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 154 286 22 1 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 154 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21
  154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 286 2 10 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 19 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 286 2 9 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 154 286 (accept_3_3 17 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 286 2 8 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 154 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 286 2 7 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 154 286 2 6 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 11 154 286 11 1 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 154 286 2 5 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 286 (Polychromatic418967fa.accept_19_9_2_1_1_2821 9 154 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 286 2 4 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 286
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 286 2 3 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 286 (accept_3_3 5 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  286 2 2 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 154 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 286 2 1 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 286 (Polychromatic418967fa.accept_18_1_10_16_1_566 1 154 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 153 286 (Eq.refl Bool.true) (allA_succ_of_accept 133 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  133 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 153 286
  (Polychromatic418967fa.accept_16_4_9_14_1_3883 132 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 131 153 286 (accept_3_3 131 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 153 286 (Polychromatic418967fa.accept_21_4_6_13_1_7137 130 153 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 153 286 (Polychromatic418967fa.accept_10_9_3_6_1_686
  129 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 153 286 (accept_3_3
  128 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 127 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 126 153 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 126 153 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 153 286 (accept_3_3 125 153 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 124 153 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 124 153 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 123 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 153 286 (accept_3_3 122 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 153 286 (Polychromatic418967fa.accept_18_12_9_16_1_4732 120 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 153 286 (accept_3_3 119 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 153 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 118 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 153 286
  (Polychromatic418967fa.accept_10_7_3_6_1_644 117 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 153 286 (accept_3_3 116 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 153 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 114 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 153 286 (accept_3_3 113 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 153 286 (Polychromatic418967fa.accept_21_7_6_13_1_10406 112
  153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 153 286 (accept_3_3 110 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 153 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 108 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 153 286 (accept_3_3 107 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 153 286 (Polychromatic418967fa.accept_25_6_3_11_1_17576 106
  153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 153 286
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 105 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 153 286 (accept_3_3 104 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 153 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 153 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 102 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 153 286 (accept_3_3 101 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 286
  (Polychromatic418967fa.accept_16_4_9_14_1_3883 100 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 153 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 153 286 (accept_3_3 98 153 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 153 286
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 96 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 153 286 (accept_3_3 95 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 153 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 94 153 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 153 286 (Polychromatic418967fa.accept_21_9_6_13_1_8777 93 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 153 286 (accept_3_3 92 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 153 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 90 153 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 153 286 (accept_3_3 89 153 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 153 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 153 286 (accept_3_3 86 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 153 286 (Polychromatic418967fa.accept_16_4_9_14_1_3883 84 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 153 286 (accept_3_3 83 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 82 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 153 286
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 81 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 153 286 (accept_3_3 80 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 153 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 78 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 153 286 (accept_3_3 77 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 286 (Polychromatic418967fa.accept_23_7_15_10_1_17575 76
  153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 153 286 (accept_3_3 74 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 153 286 (Polychromatic418967fa.accept_21_9_6_13_1_8777 72 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 286 (accept_3_3 71 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 286 (Polychromatic418967fa.accept_21_7_6_13_1_10406 70 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 286
  (Polychromatic418967fa.accept_10_9_3_6_1_686 69 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 153 286 (accept_3_3 68 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 153 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 286 (accept_3_3 65 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 64 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 153 286 (accept_3_3 62 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 153 286 (Polychromatic418967fa.accept_21_18_6_13_1_7148 60 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 286 (accept_3_3 59 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 286
  (Polychromatic418967fa.accept_10_7_3_6_1_644 57 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 153 286 (accept_3_3 56 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 153 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 286 (accept_3_3 53 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 286 (Polychromatic418967fa.accept_16_4_9_14_1_3883 52 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 153 286 (accept_3_3 50 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 153 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 286 (accept_3_3 47 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 286 (Polychromatic418967fa.accept_21_4_6_13_1_7137 46 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 286
  (Polychromatic418967fa.accept_21_3_6_13_1_8756 45 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 153 286 (accept_3_3 44 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 153 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 286 (accept_3_3 41 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 40 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 153 286 (accept_3_3 38 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 153 286 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 286 (accept_3_3 35 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 286
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 33 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 153 286 (accept_3_3 32 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 153 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 286 (accept_3_3 29 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 153
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 286 (accept_3_3 26 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 286 (Polychromatic418967fa.accept_21_3_6_13_1_8756 24 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 286 (accept_3_3 23 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 286 (Polychromatic418967fa.accept_27_22_18_16_1_15790 22
  153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 286
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 21 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 286 (accept_3_3 20 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 153 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 286 (accept_3_3 17 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 286 (Polychromatic418967fa.accept_21_16_6_13_1_10430 16
  153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 286 (accept_3_3 14 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 286 (accept_3_3 11 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 286 (Polychromatic418967fa.accept_33_10_21_22_1_17574 10
  153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 286
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 286 (accept_3_3 8 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 153 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 286 (accept_3_3 5 153 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 153 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 286 (accept_3_3 2 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 135 152 286 (Eq.refl Bool.true) (allA_of_3_1 135 152 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 136 151 286 (Eq.refl Bool.true) (allA_succ_of_accept 135 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 135 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 151 286 (accept_3_3 134 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  133 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 133 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 151 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 132 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 151 286 (accept_3_3 131 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 151 286 (Polychromatic418967fa.accept_18_4_7_16_1_2307 130
  151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 129 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 151 286 (accept_3_3 128 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 151 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 127 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 151 286 (Polychromatic418967fa.accept_19_12_18_1_1_12336 126 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 151 286 (accept_3_3 125 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 151 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 124 151
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 151 286 (accept_3_3 122 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 151 286 (Polychromatic418967fa.accept_19_6_18_1_1_17527 120 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 151 286 (accept_3_3 119 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 151 286 (Polychromatic418967fa.accept_17_16_15_14_1_6747 118
  151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 117 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 151 286 (accept_3_3 116 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 151 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 115 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 151 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 114 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 151 286 (accept_3_3 113 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 151 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 112 151
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 151 286 (accept_3_3 110 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 151 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 108 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 151 286 (accept_3_3 107 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 151 286 (Polychromatic418967fa.accept_16_10_7_14_1_2882 106
  151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 151 286 (accept_3_3 104 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 151 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 103 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 151 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 102 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 151 286 (accept_3_3 101 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 151 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 100 151
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 151 286 (accept_3_3 98 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 151 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 151 286 (accept_3_3 95 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 151 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 94 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 151 286 (accept_3_3 92 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 151 286 (Polychromatic418967fa.accept_17_6_15_14_1_8027 91 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 151 286 (Polychromatic418967fa.accept_16_10_7_14_1_2882 90 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 151 286 (accept_3_3 89 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 151 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 151
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 151 286 (accept_3_3 86 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 151 286 (Polychromatic418967fa.accept_16_4_7_14_1_3897 84 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 286 (accept_3_3 83 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 151 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 151 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 151 286 (accept_3_3 80 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 151 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 151 286 (Polychromatic418967fa.accept_19_2_18_1_1_8275 78 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 286 (accept_3_3 77 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 151
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 286 (accept_3_3 74 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 286 (accept_3_3 71 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 286 (Polychromatic418967fa.accept_19_13_18_1_1_8215 70 151 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 286 (accept_3_3 68 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 286 (accept_3_3 65 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 286 (accept_3_3 62 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 286 (Polychromatic418967fa.accept_21_18_4_13_1_5602 60 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 286 (accept_3_3 59 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 151 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 286 (accept_3_3 56 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 286 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 286 (accept_3_3 53 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 286 (accept_3_3 50 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 286 (Polychromatic418967fa.accept_21_6_4_13_1_8740 48 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 286 (accept_3_3 47 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 286 (Polychromatic418967fa.accept_17_12_15_14_1_6746 46
  151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 286 (accept_3_3 44 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 286 (Polychromatic418967fa.accept_19_5_18_1_1_11052 43 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 286 (accept_3_3 41 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 151 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 286 (accept_3_3 38 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 286 (Polychromatic418967fa.accept_16_4_7_14_1_3897 36 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 286 (accept_3_3 35 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 286 (Polychromatic418967fa.accept_20_14_11_6_1_6264 34 151
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 286 (accept_3_3 32 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 286 (accept_3_3 29 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 286 (accept_3_3 26 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 286 (accept_3_3 23 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 286 (accept_3_3 20 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 286 (Polychromatic418967fa.accept_21_18_4_13_1_5602 18 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 286 (accept_3_3 17 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 151 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 286 (accept_3_3 14 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 286 (accept_3_3 11 151 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 286 (accept_3_3 8 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 286 (Polychromatic418967fa.accept_17_6_15_14_1_8027 6 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 286 (accept_3_3 5 151 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 151 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 286 (accept_3_3 2 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 137 150 286 (Eq.refl Bool.true) (allA_succ_of_gcd 136 150 286 2 68 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 150 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 135 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 134 150 286 2 67 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 133 150 286 (Polychromatic418967fa.accept_24_13_6_22_1_2345 133 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 150 286 2 66 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 150 286 (accept_3_3 131 150 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 150 286 2 65 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 150 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 129 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 150 286 2 64 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 150 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 127 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 150 286 2 63 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 150 286 (accept_3_3 125 150 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 150 286 2 62 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 150 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 123 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 150 286 2 61 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 150 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 121 150 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 150 286 2 60 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 150 286 (accept_3_3 119 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 150 286 2 59 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 150 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 117 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 150 286 2 58 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 150 286 (Polychromatic418967fa.accept_14_3_10_6_1_1136 115 150 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 150 286 2 57 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 150 286 (accept_3_3
  113 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 150 286 2 56 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 150 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 111 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 150 286 2 55 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 150 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 109 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 150 286 2 54 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 150 286 (accept_3_3 107 150 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 150 286 2 53 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 150 286
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 105 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 150 286 2 52 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 150 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 103 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 150 286 2 51 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 150 286 (accept_3_3 101 150 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 150 286 2 50 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 150 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 99 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 150 286 2 49 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 150 286 (Polychromatic418967fa.accept_23_5_12_10_1_17573 97 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 286 2 48 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 150 286 (accept_3_3 95 150 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 150 286 2 47 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 150 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 93 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 150 286 2 46 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 150 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 150 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 150 286 2 45 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 150 286 (accept_3_3 89 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 150 286 2 44 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 150 286 (Polychromatic418967fa.accept_12_3_6_10_1_576
  87 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 150 286 2 43 75 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 150 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 85 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 150 286 2 42 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 150 286 (accept_3_3 83 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 150 286 2 41 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 150 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 150 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 150 286 2 40 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 286 2 39 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 286 (accept_3_3 77 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 150 286 2 38 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 150 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 150 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 150 286 2 37 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 286 2 36 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 286 (accept_3_3 71 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 150 286 2 35 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 150 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 150 286 2 34 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 286 2 33 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 286 (accept_3_3 65 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 150 286 2 32 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 150 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 150 286 2 31 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 286
  (Polychromatic418967fa.accept_19_4_17_1_1_4009 61 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 286 2 30 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 286 (accept_3_3 59 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 150 286 2 29 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 150 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 150 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 150 286 2 28 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 286 2 27 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 286 (accept_3_3 53 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 286 2 26 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 150 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 150 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 150 286 2 25 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 286 2 24 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 286 (accept_3_3 47 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 286 2 23 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 150 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 150 286 2 22 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 286
  (Polychromatic418967fa.accept_31_12_26_7_1_17572 43 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 150 286 2 21 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 150 286 (accept_3_3 41 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 286 2 20 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 150 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 286 2 19 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 286 2 18 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 286 (accept_3_3 35 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 286 2 17 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 150 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 286 2 16 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 286 2 15 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 286 (accept_3_3 29 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 286 2 14 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 286 2 13 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 286 2 12 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 286 (accept_3_3 23 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 286 2 11 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 150 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 150 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 286 2 10 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 286 2 9 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 286 (accept_3_3 17 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 286 2 8 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 150 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 150 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 286 2 7 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 286 2 6 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 286 (accept_3_3 11 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 286 2 5 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 150 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 286 2 4 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 286
  (Polychromatic418967fa.accept_27_7_15_16_1_17571 7 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 150 286 2 3 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 150 286 (accept_3_3 5 150 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 150 286 2 2 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 150 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 150 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 286 2 1 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  150 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 138 149 286 (Eq.refl Bool.true) (allA_of_3_1 138 149 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 139 148 286 (Eq.refl Bool.true) (allA_succ_of_gcd 138 148 286 2 69 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 137 148 286 (accept_3_3 137 148 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 148 286 2 68 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 148 286 (Polychromatic418967fa.accept_7_2_1_6_1_173
  135 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 148 286 2 67 74 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 148 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 133 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 148 286 2 66 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 148 286 (accept_3_3 131 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 148 286 2 65 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 148 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 129 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 148 286 2 64 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 148 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 127 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 148 286 2 63 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 148 286 (accept_3_3 125 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 148 286 2 62 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 148 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 123 148 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 148 286 2 61 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 148 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 121 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 148 286 2 60 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 148 286 (accept_3_3 119 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 148 286 2 59 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 148 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 117 148 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 148 286 2 58 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 148 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 115 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 148 286 2 57 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 148 286 (accept_3_3 113 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 148 286 2 56 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 148 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 111 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 148 286 2 55 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 148 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 109 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 148 286 2 54 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 148 286 (accept_3_3 107 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 148 286 2 53 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 148 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 105 148 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 148 286 2 52 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 148 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 103 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 148 286 2 51 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 148 286 (accept_3_3 101 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 148 286 2 50 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 148 286 (Polychromatic418967fa.accept_19_4_15_1_1_2819 99 148 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 148 286 2 49 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 148 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 97 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 148 286 2 48 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 148 286 (accept_3_3 95 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 148 286 2 47 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 148 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 148 286 2 46 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 148 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 91 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 148 286 2 45 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 148 286 (accept_3_3 89 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 148 286 2 44 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 148 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 87 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 148 286 2 43 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 148 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 85 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 148 286 2 42 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 148 286 (accept_3_3 83 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 148 286 2 41 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 148 286 (Polychromatic418967fa.accept_16_1_4_14_1_1896 81 148 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 148 286 2 40 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 148 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 148 286 2 39 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 148 286 (accept_3_3 77 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 286 2 38 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 286 2 37 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 286 2 36 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 286 (accept_3_3 71 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 286 2 35 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 286 2 34 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 286 2 33 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 286 (accept_3_3 65 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 286 2 32 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 286 2 31 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 286 2 30 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 286 (accept_3_3 59 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 286 2 29 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 286 2 28 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 286 2 27 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 286 (accept_3_3 53 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 286 2 26 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 286 2 25 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 286 2 24 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 286 (accept_3_3 47 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 286 2 23 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 286 (Polychromatic418967fa.accept_17_11_12_14_1_5431 45 148 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 286 2 22 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 286 2 21 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 286 (accept_3_3 41 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 286 2 20 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 286 2 19 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 286 2 18 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 148 286 (accept_3_3 35 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 286 2 17 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 286 2 16 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 148 286 2 15 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 148 286 (accept_3_3 29 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 286 2 14 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 148 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 148 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 286 2 13 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 286 2 12 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 148 286 (accept_3_3 23 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 286 2 11 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 286 2 10 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 286 2 9 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 286 (accept_3_3 17 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 286 2 8 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 148 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 286 2 7 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 148 286 2 6 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 148 286 (accept_3_3 11 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 286 2 5 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 148 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 286 2 4 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 148 286 2 3 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 286 (accept_3_3 5 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  286 2 2 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 148 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 286 2 1 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 148 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 140 147 286 (Eq.refl Bool.true) (allA_succ_of_accept 139 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  139 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 147 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 138 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 137 147 286 (accept_3_3 137 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  136 147 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 136 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 135 147 286 (Polychromatic418967fa.accept_17_16_11_14_1_4213 135 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 147 286 (accept_3_3 134 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 133 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 147 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 132 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 147 286 (accept_3_3 131 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  130 147 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 130 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 129 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 147 286 (accept_3_3 128 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 127 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 127 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 147 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 126 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 147 286 (accept_3_3 125 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 147 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 124 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 123 147 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 123 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 147 286 (accept_3_3 122 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 147 286
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 120 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 147 286 (accept_3_3 119 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 147 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 118 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 147 286 (accept_3_3 116 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 115 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 147 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 114 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 147 286 (accept_3_3 113 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 147 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 112 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 147 286 (Polychromatic418967fa.accept_10_1_7_6_1_91 111 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 147 286 (accept_3_3 110 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 147 286
  (Polychromatic418967fa.accept_19_13_14_1_1_3996 108 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 147 286 (accept_3_3 107 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 147 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 106 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3
  105 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 147 286 (accept_3_3
  104 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 103 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 147 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 102 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 147 286 (accept_3_3 101 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 147 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 100 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 147 286
  (Polychromatic418967fa.accept_14_1_7_6_1_3604 99 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 147 286 (accept_3_3 98 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 147 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 96 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 147 286 (accept_3_3 95 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 147 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 147 286 (accept_3_3 92 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 147 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 90 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 286 (accept_3_3 89 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 286 (Polychromatic418967fa.accept_15_13_12_1_1_1841 88 147
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 147 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 87 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 147 286 (accept_3_3 86 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 147 286 (Polychromatic418967fa.accept_17_16_11_14_1_4213 84 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 286 (accept_3_3 83 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 147 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 147 286 (accept_3_3 80 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 147 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 78 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 286 (accept_3_3 77 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 286
  (Polychromatic418967fa.accept_16_11_3_14_1_5043 75 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 147 286 (accept_3_3 74 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 147 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 286 (Polychromatic418967fa.accept_19_15_14_1_1_8297 72 147
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 286 (accept_3_3 71 147
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 286
  (Polychromatic418967fa.accept_19_13_14_1_1_3996 70 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 286 (accept_3_3 68 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 66 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 147 286 (accept_3_3 65 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 147 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 147 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 286 (accept_3_3 62 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 147 286 (accept_3_3 59 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 147 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 286 (accept_3_3 56 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 147 286 (accept_3_3 53 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 147 286 (Polychromatic418967fa.accept_20_12_7_6_1_6154 52 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 147 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 286 (accept_3_3 50 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 286
  (Polychromatic418967fa.accept_19_10_14_1_1_8296 48 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 147 286 (accept_3_3 47 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 147 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 286 (accept_3_3 44 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 147 286 (accept_3_3 41 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 147 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 147 286 (Polychromatic418967fa.accept_20_19_7_6_1_6255 39 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 286 (accept_3_3 38 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 286
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 147 286 (accept_3_3 35 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 147 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 286 (accept_3_3 32 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 286 (accept_3_3 29 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 147 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 147 286 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 286 (accept_3_3 26 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 286 (accept_3_3 23 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 147 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 286 (accept_3_3 20 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 286 (accept_3_3 17 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 286 (Polychromatic418967fa.accept_17_16_11_14_1_4213 16 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 286 (accept_3_3 14 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 286
  (Polychromatic418967fa.accept_17_12_11_14_1_3120 12 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 286 (accept_3_3 11 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 147 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 286 (accept_3_3 8 147 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 286 (accept_3_3 5 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 147 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 286 (accept_3_3 2 147 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 141 146 286 (Eq.refl Bool.true) (allA_of_3_1 141 146 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 142 145 286 (Eq.refl Bool.true) (allA_succ_of_accept 141 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 141 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 140 145 286 (accept_3_3 140 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  139 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 139 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 138 145 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 138 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 145 286 (accept_3_3 137 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 145 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 136 145
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 135 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 145 286 (accept_3_3 134 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  133 145 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 133 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 132 145 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 132 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 145 286 (accept_3_3 131 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 145 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 130 145
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 129 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 145 286 (accept_3_3 128 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 127 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 145 286 (Polychromatic418967fa.accept_15_6_10_1_1_3675 126 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 145 286 (accept_3_3 125 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 145 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 124 145
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 123 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 145 286 (accept_3_3 122 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 145 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 121 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 145 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 120 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 145 286 (accept_3_3 119 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 145 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 118
  145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 145 286 (accept_3_3 116 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 145 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 114 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 145 286 (accept_3_3 113 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 145 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 112 145
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 145 286 (accept_3_3 110 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 145 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 109 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 145 286 (Polychromatic418967fa.accept_19_13_12_1_1_3993 108 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 145 286 (accept_3_3 107 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 145 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 106 145
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 145 286 (accept_3_3 104 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 145 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 102 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 145 286 (accept_3_3 101 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 145 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 100 145
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 145 286 (accept_3_3 98 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 145 286 (Polychromatic418967fa.accept_14_13_5_6_1_2747 97 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 145 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 145 286 (accept_3_3 95 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 145 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 145 286 (accept_3_3 92 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 145 286 (Polychromatic418967fa.accept_17_5_9_14_1_4282 90 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 145 286 (accept_3_3 89 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 145 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 145 286 (accept_3_3 86 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 145 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 145 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 286 (accept_3_3 83 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 82 145 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 145 286 (accept_3_3 80 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 145 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 286 (accept_3_3 77 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 145 286 (accept_3_3 74 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 145 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 73 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 145 286 (Polychromatic418967fa.accept_17_4_9_14_1_5406 72 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 286 (accept_3_3 71 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 145 286 (Polychromatic418967fa.accept_19_13_12_1_1_3993 70 145
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 286 (accept_3_3 68 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 286 (accept_3_3 65 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 286 (accept_3_3 62 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 61 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 145 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 286 (accept_3_3 59 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 286 (accept_3_3 56 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 145 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 286 (accept_3_3 53 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 145
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 286 (accept_3_3 50 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 286 (accept_3_3 47 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 286 (accept_3_3 44 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 286 (accept_3_3 41 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 286 (accept_3_3 38 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 286 (accept_3_3 35 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 286 (accept_3_3 32 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 286 (accept_3_3 29 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 286 (accept_3_3 26 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 286 (accept_3_3 23 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 286 (accept_3_3 20 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 286 (accept_3_3 17 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 286 (accept_3_3 14 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 286 (accept_3_3 11 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 286 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 145 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 286 (accept_3_3 8 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 286 (accept_3_3 5 145 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 145 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 286 (accept_3_3 2 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 143 144 286 (Eq.refl Bool.true) (allA_succ_of_gcd 142 144 286 2 71 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 141 144 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 141 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 140 144 286 2 70 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 139 144 286 (Polychromatic418967fa.accept_19_6_11_1_1_6815 139 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 138 144 286 2 69 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 137 144 286 (accept_3_3 137 144 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 136 144 286 2 68 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 135 144 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 135 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 134 144 286 2 67 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 133 144 286 (Polychromatic418967fa.accept_21_7_18_13_1_5585 133 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 144 286 2 66 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 144 286 (accept_3_3 131 144 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 144 286 2 65 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 144 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 129 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 144 286 2 64 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 144 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 127 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 144 286 2 63 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 144 286 (accept_3_3 125 144 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 144 286 2 62 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 144 286
  (Polychromatic418967fa.accept_19_9_11_1_1_8239 123 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 122 144 286 2 61 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 121 144 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 121 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 144 286 2 60 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 144 286 (accept_3_3 119 144 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 144 286 2 59 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 144 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 117 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 144 286 2 58 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 144 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 115 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 144 286 2 57 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 144 286 (accept_3_3 113 144 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 144 286 2 56 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 144 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 111 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 144 286 2 55 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 144 286 (Polychromatic418967fa.accept_17_7_8_14_1_6720 109 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 144 286 2 54 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 144 286 (accept_3_3 107 144 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 144 286 2 53 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 144 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 105 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 144 286 2 52 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 144 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 103 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 144 286 2 51 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 144 286 (accept_3_3 101 144 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 144 286 2 50 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 144 286
  (Polychromatic418967fa.accept_21_15_18_13_1_8747 99 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 144 286 2 49 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 144 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 97 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 144 286 2 48 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 286 (accept_3_3 95 144 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 144 286 2 47 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 144 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 93 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 144 286 2 46 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 144 286 (Polychromatic418967fa.accept_17_6_8_14_1_6706 91 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 144 286 2 45 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 144 286 (accept_3_3 89 144 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 144 286 2 44 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 144 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 144 286 2 43 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 144 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 85 144 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 144 286 2 42 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 144 286 (accept_3_3 83 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 286 2 41 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 144 286 (Polychromatic418967fa.accept_15_6_9_1_1_1823
  81 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 144 286 2 40 72 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 79 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 286 2 39 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 286 (accept_3_3 77 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 144 286 2 38 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 144 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 144 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 144 286 2 37 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 286 2 36 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 286 (accept_3_3 71 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 144 286 2 35 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 144 286 (Polychromatic418967fa.accept_19_12_11_1_1_4036 69 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 144 286 2 34 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 286
  (Polychromatic418967fa.accept_15_7_9_1_1_473 67 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 286 2 33 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 286 (accept_3_3 65 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 286 2 32 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 144 286 (Polychromatic418967fa.accept_19_6_11_1_1_6815 63 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 144 286 2 31 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 286 2 30 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 286 (accept_3_3 59 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 144 286 2 29 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 144 286 (Polychromatic418967fa.accept_17_6_8_14_1_6706 57 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 144 286 2 28 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 286 2 27 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 286 (accept_3_3 53 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 144 286 2 26 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 144 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 144 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 286 2 25 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 286
  (Polychromatic418967fa.accept_21_7_18_13_1_5585 49 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 144 286 2 24 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 144 286 (accept_3_3 47 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 286 2 23 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 144 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 144 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 286 2 22 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 286
  (Polychromatic418967fa.accept_23_20_6_10_1_17570 43 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 144 286 2 21 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 144 286 (accept_3_3 41 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 286 2 20 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 144 286 (Polychromatic418967fa.accept_23_16_6_10_1_7930 39 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 286 2 19 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 286 2 18 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 286 (accept_3_3 35 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 144 286 2 17 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 144 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 144 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 286 2 16 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 286 2 15 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 286 (accept_3_3 29 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 286 2 14 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 144 286 (Polychromatic418967fa.accept_19_8_11_1_1_8320 27 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 286 2 13 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 286 2 12 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 286 (accept_3_3 23 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 286 2 11 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 144 286 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 286 2 10 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 286 2 9 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 286 (accept_3_3 17 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 286 2 8 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 144 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 144 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 286 2 7 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 286
  (Polychromatic418967fa.accept_27_13_9_16_1_17514 13 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 144 286 2 6 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 144 286 (accept_3_3 11 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 286 2 5 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 144 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 286 2 4 72 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 286
  (Polychromatic418967fa.accept_15_7_9_1_1_473 7 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 286 2 3 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 286 (accept_3_3 5 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144
  286 2 2 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  144 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 144 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 144 286 2 1 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 144 286 (Polychromatic418967fa.accept_25_1_19_11_1_17569 1 144 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 143 286 (allA_of_3_1 143 143 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 142 286
  (allA_succ_of_accept 141 142 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 141 142 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 140 142 286 2 70 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 139 142 286
  (Polychromatic418967fa.accept_17_3_6_14_1_4312 139 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 138 142 286 2 69 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 137 142 286 (accept_3_3 137 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 136 142 286 2 68 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 135 142 286 (Polychromatic418967fa.accept_19_2_9_1_1_4029 135 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 142 286 2 67 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 142 286
  (Polychromatic418967fa.accept_21_7_16_13_1_2733 133 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 132 142 286 2 66 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 131 142 286 (accept_3_3 131 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 142 286 2 65 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 142 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 129 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 142 286 2 64 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 142 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 127 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 142 286 2 63 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 142 286 (accept_3_3 125 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 142 286 2 62 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 142 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 123 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 142 286 2 61 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 142 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 121 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 142 286 2 60 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 142 286 (accept_3_3 119 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 142 286 2 59 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 142 286 (Polychromatic418967fa.accept_17_15_6_14_1_4239 117 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 142 286 2 58 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 142 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 115 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 142 286 2 57 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 142 286 (accept_3_3 113 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 142 286 2 56 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 142 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 111 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 142 286 2 55 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 142 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 109 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 142 286 2 54 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 142 286 (accept_3_3 107 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 142 286 2 53 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 142 286 (Polychromatic418967fa.accept_17_3_6_14_1_4312 105 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 142 286 2 52 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 142 286
  (Polychromatic418967fa.accept_19_8_9_1_1_3990 103 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 142 286 2 51 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 142 286 (accept_3_3 101 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 142 286 2 50 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 142 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 142 286 2 49 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 142 286
  (Polychromatic418967fa.accept_19_2_9_1_1_4029 97 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 142 286 2 48 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 142 286 (accept_3_3 95 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 142 286 2 47 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 142 286 (Polychromatic418967fa.accept_17_8_6_14_1_6718 93 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 142 286 2 46 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 142 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 91 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 142 286 2 45 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 142 286 (accept_3_3 89 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 142 286 2 44 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 142 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 142 286 2 43 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 142 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 142 286 2 42 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 142 286 (accept_3_3 83 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 142 286 2 41 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 142 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 286 2 40 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 286
  (Polychromatic418967fa.accept_25_4_17_11_1_17568 79 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 142 286 2 39 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 142 286 (accept_3_3 77 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 286 2 38 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 286 (Polychromatic418967fa.accept_17_7_6_14_1_6737 75 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 286 2 37 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 286 2 36 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 286 (accept_3_3 71 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 286 2 35 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 69 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 286 2 34 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 286 2 33 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 286 (accept_3_3 65 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 286 2 32 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 286 (Polychromatic418967fa.accept_23_17_4_10_1_9674 63 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 286 2 31 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 286 2 30 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 286 (accept_3_3 59 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 286 2 29 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 286 2 28 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 286
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 286 2 27 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 286 (accept_3_3 53 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 286 2 26 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 286 2 25 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 286
  (Polychromatic418967fa.accept_17_15_6_14_1_4239 49 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 142 286 2 24 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 142 286 (accept_3_3 47 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 286 2 23 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 286 2 22 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 286 2 21 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 286 (accept_3_3 41 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 286 2 20 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 286 2 19 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 286
  (Polychromatic418967fa.accept_17_3_6_14_1_4312 37 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 286 2 18 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 286 (accept_3_3 35 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 286 2 17 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 286 (Polychromatic418967fa.accept_19_14_9_1_1_8315 33 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 286 2 16 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 286 2 15 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 286 (accept_3_3 29 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 286 2 14 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 286 (Polychromatic418967fa.accept_19_8_9_1_1_3990 27 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 286 2 13 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 286 2 12 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 286 (accept_3_3 23 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 286 2 11 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 286 2 10 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 286
  (Polychromatic418967fa.accept_21_19_16_13_1_4099 19 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 142 286 2 9 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 142 286 (accept_3_3 17 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 286 2 8 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 286 2 7 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 286
  (Polychromatic418967fa.accept_23_13_4_10_1_17567 13 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 142 286 2 6 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 142 286 (accept_3_3 11 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 286 2 5 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 142 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 286 2 4 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 286
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 7 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 286 2 3 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 286 (accept_3_3 5 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  286 2 2 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 142 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 286 2 1 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 142 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 141 286 (allA_succ_of_accept 140 141 286 (accept_3_3 140 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 139 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 139 141 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 141 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 138 141
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 141 286 (accept_3_3 137 141
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 141 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 136 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 135 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 135 141 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 141 286 (accept_3_3 134 141 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 133 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 141 286 (Polychromatic418967fa.accept_10_2_1_6_1_634
  132 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 141 286 (accept_3_3
  131 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 141 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 130 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 141 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 129 141 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 141 286 (accept_3_3 128 141 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 127 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 127 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 141 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 126 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 141 286 (accept_3_3 125 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 141 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 124 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 123 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 141 286 (accept_3_3 122 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 141 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 141 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 120 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 141 286 (accept_3_3 119 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 141 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 118 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 141 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 117 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 141 286 (accept_3_3 116 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 141
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 141 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 114 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 141 286 (accept_3_3 113 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 141 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 112 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 141 286 (accept_3_3 110 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 141 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 141 286
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 108 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 141 286 (accept_3_3 107 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 141 286 (Polychromatic418967fa.accept_16_10_13_14_1_5042 106 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 141 286 (Polychromatic418967fa.accept_10_5_1_6_1_672 105 141 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 141 286 (accept_3_3 104 141 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62
  103 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 141 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 102 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 141 286 (accept_3_3 101 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 141 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 100 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 141 286 (accept_3_3 98 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 96 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 141 286 (accept_3_3 95 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 141 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 94 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 141 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 141 286 (accept_3_3 92 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 90 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 141 286 (accept_3_3 89 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 141 286 (Polychromatic418967fa.accept_19_12_8_1_1_11059 88 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 286 (accept_3_3 86 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 141 286 (accept_3_3 83 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 141 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 141 286 (Polychromatic418967fa.accept_16_1_13_14_1_1064 81 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 286 (accept_3_3 80 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 141 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 78 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 141 286 (accept_3_3 77 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 141 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 286 (accept_3_3 74 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 141 286 (accept_3_3 71 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 141 286 (Polychromatic418967fa.accept_15_10_6_1_1_3707 70 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 69 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 286 (accept_3_3 68 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 141 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 286 (accept_3_3 65 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 286 (accept_3_3 62 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 286
  (Polychromatic418967fa.accept_17_9_5_14_1_4277 60 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 141 286 (accept_3_3 59 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 141 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 141 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 286 (accept_3_3 56 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 286 (accept_3_3 53 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 286 (accept_3_3 50 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 141 286 (accept_3_3 47 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 141 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 141 286 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 286 (accept_3_3 44 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 141 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 286
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 286 (accept_3_3 41 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 286 (accept_3_3 38 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 286
  (Polychromatic418967fa.accept_17_2_5_14_1_2068 36 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 141 286 (accept_3_3 35 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 141 286 (Polychromatic418967fa.accept_19_15_8_1_1_6794 34 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 141 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 286 (accept_3_3 32 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 286 (accept_3_3 29 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 286 (accept_3_3 26 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 286
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 286 (accept_3_3 23 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 286 (accept_3_3 20 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 286 (accept_3_3 17 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 286 (accept_3_3 14 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 286 (accept_3_3 11 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 286 (accept_3_3 8 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 286 (accept_3_3 5 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 141 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 286 (accept_3_3 2 141 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 140 286 (allA_of_3_1 140 140 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 139 286
  (allA_succ_of_accept 138 139 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 138 139 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 139 286 (accept_3_3 137 139 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 136 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 136 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 139 286 (Polychromatic418967fa.accept_6_3_1_4_1_25
  135 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 139 286 (accept_3_3
  134 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 133 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 132 139 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 132 139 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 139 286 (accept_3_3 131 139 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 130 139 286 (Polychromatic418967fa.accept_17_11_3_14_1_6736 130 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 129 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 139 286 (accept_3_3 128 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 127 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 139 286 (Polychromatic418967fa.accept_23_11_1_10_1_17566 126 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 139 286 (accept_3_3 125 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 139 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 124 139
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 139 286 (accept_3_3 122 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 139 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 120 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 139 286 (accept_3_3 119 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 118 139 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 117 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 139 286 (accept_3_3 116 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 139 286 (Polychromatic418967fa.accept_10_5_9_6_1_697 115 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 139 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 114 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 139 286 (accept_3_3 113 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 139 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 112 139
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 139 286 (accept_3_3 110 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 139 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 108 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 139 286 (accept_3_3 107 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 139 286 (Polychromatic418967fa.accept_19_11_6_1_1_2826 106
  139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 139 286 (accept_3_3 104 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 139 286 (Polychromatic418967fa.accept_10_3_9_6_1_94 103 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 139 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 102 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 139 286 (accept_3_3 101 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 139 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 139 286 (accept_3_3 98 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 139 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 286 (accept_3_3 95 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 286 (Polychromatic418967fa.accept_19_18_6_1_1_12398 94 139 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 286 (accept_3_3 92 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 286 (Polychromatic418967fa.accept_19_14_6_1_1_4022 90 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 286 (accept_3_3 89 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 139
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 286 (accept_3_3 86 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 286 (accept_3_3 83 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 286 (accept_3_3 80 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 286 (Polychromatic418967fa.accept_17_11_3_14_1_6736 79 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 78 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 286 (accept_3_3 77 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 286 (accept_3_3 74 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 286 (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 286 (accept_3_3 71 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 286 (Polychromatic418967fa.accept_17_2_3_14_1_8043 70 139
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 286 (accept_3_3 68 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 286 (Polychromatic418967fa.accept_16_3_11_14_1_446 67 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 286 (accept_3_3 65 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 286 (accept_3_3 62 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 286 (accept_3_3 59 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 286 (Polychromatic418967fa.accept_33_25_7_22_1_17565 58 139 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 286 (accept_3_3 56 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 286 (accept_3_3 53 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 139
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 286 (accept_3_3 50 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 286 (accept_3_3 47 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 286 (accept_3_3 44 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 286 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 286 (accept_3_3 41 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 286 (accept_3_3 38 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 286 (Polychromatic418967fa.accept_17_2_3_14_1_8043 36 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 286 (accept_3_3 35 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 286 (Polychromatic418967fa.accept_20_14_19_6_1_12003 34
  139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 286 (accept_3_3 32 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 286 (Polychromatic418967fa.accept_24_7_19_22_1_16006 31 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 286 (accept_3_3 29 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 139 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 286 (accept_3_3 26 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 286 (accept_3_3 23 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 286 (Polychromatic418967fa.accept_19_3_6_1_1_4064 22 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 286 (accept_3_3 20 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 286 (accept_3_3 17 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 139
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 286 (accept_3_3 14 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 286 (accept_3_3 11 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 286 (accept_3_3 8 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 286 (Polychromatic418967fa.accept_14_7_13_6_1_1177 7 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 286 (accept_3_3 5 139 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 139 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 286 (accept_3_3 2 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 138 286 (allA_succ_of_accept 137 138 286 (accept_3_3 137 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 136 138 286 2 68 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 135 138 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 135 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 138 286 2 67 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 138 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 133 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 138 286 2 66 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 138 286 (accept_3_3 131 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 138 286 2 65 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 138 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 129 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 138 286 2 64 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 138 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 127 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 138 286 2 63 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 138 286 (accept_3_3 125 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 138 286 2 62 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 138 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 123 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 138 286 2 61 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 138 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 121 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 138 286 2 60 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 138 286 (accept_3_3 119 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 138 286 2 59 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 138 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 117 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 138 286 2 58 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 138 286
  (Polychromatic418967fa.accept_25_15_13_11_1_17564 115 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 138 286 2 57 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 138 286 (accept_3_3 113 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 138 286 2 56 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 138 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 111 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 138 286 2 55 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 138 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 109 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 138 286 2 54 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 138 286 (accept_3_3 107 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 138 286 2 53 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 138 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 105 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 138 286 2 52 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 138 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 103 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 138 286 2 51 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 138 286 (accept_3_3 101 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 138 286 2 50 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 138 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 138 286 2 49 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 138 286
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 97 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 138 286 2 48 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 138 286 (accept_3_3 95 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 138 286 2 47 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 138 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 93 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 138 286 2 46 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 138 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 286 2 45 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 286 (accept_3_3 89 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 138 286 2 44 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 138 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 138 286 2 43 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 138 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 85 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 286 2 42 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 286 (accept_3_3 83 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 138 286 2 41 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 138 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 138 286 2 40 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 138 286
  (Polychromatic418967fa.accept_15_4_3_1_1_487 79 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 286 2 39 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 286 (accept_3_3 77 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 138 286 2 38 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 138 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 75 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 138 286 2 37 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 286 2 36 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 286 (accept_3_3 71 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 138 286 2 35 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 138 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 138 286 2 34 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 286 2 33 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 286 (accept_3_3 65 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 286 2 32 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 138 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 138 286 2 31 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 286
  (Polychromatic418967fa.accept_16_13_10_14_1_2871 61 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 138 286 2 30 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 138 286 (accept_3_3 59 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 138 286 2 29 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 138 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 138 286 2 28 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 286 2 27 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 286 (accept_3_3 53 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 286 2 26 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 286 2 25 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 286 2 24 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 286 (accept_3_3 47 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 286 2 23 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 138 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 286 2 22 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 286 2 21 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 286 (accept_3_3 41 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 286 2 20 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 138 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 286 2 19 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 286 2 18 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 286 (accept_3_3 35 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 286 2 17 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 286 2 16 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 286 2 15 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 286 (accept_3_3 29 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 286 2 14 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 286 2 13 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 286 2 12 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 286 (accept_3_3 23 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 286 2 11 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 286 2 10 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 286 2 9 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 286 (accept_3_3 17 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 286 2 8 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 138 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 286 2 7 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 286 2 6 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 286 (accept_3_3 11 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 286 2 5 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 138 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 138 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 286 2 4 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 286
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 286 2 3 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 286 (accept_3_3 5 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138
  286 2 2 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  138 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 138 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 138 286 2 1 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 138 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 138 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 137 286 (allA_of_3_1 137 137 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 136 286
  (allA_succ_of_accept 135 136 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 135 136 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 134 136 286 2 67 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 136 286 (Polychromatic418967fa.accept_12_1_4_10_1_209
  133 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 136 286 2 66 68 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 136 286
  (accept_3_3 131 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 136 286 2 65 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 136 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 129 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 136 286 2 64 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 136 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 127 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 136 286 2 63 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 136 286 (accept_3_3 125 136 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 136 286 2 62 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 136 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 123 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 136 286 2 61 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 136 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 121 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 136 286 2 60 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 136 286 (accept_3_3 119 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 136 286 2 59 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 136 286
  (Polychromatic418967fa.accept_20_17_16_6_1_14775 117 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 136 286 2 58 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 136 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 115 136 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 136 286 2 57 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 136 286 (accept_3_3
  113 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 136 286 2 56 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 136 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 111 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 136 286 2 55 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 136 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 109 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 136 286 2 54 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 136 286 (accept_3_3 107 136 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 136 286 2 53 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 136 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 105 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 136 286 2 52 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 136 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 103 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 136 286 2 51 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 136 286 (accept_3_3 101 136 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 136 286 2 50 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 136 286
  (Polychromatic418967fa.accept_19_4_3_1_1_17563 99 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 136 286 2 49 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 136 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 97 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 136 286 2 48 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 136 286 (accept_3_3 95 136 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 136 286 2 47 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 136 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 93 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 136 286 2 46 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 136 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 91 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 136 286 2 45 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 136 286 (accept_3_3 89 136 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 136 286 2 44 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 136 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 87 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 136 286 2 43 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 136 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 136 286 2 42 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 136 286 (accept_3_3 83 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 136 286 2 41 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 136 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 81
  136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 286 2 40 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 286 2 39 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 286 (accept_3_3 77 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 286 2 38 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 286 2 37 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 136 286 2 36 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 136 286 (accept_3_3 71 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 136 286 2 35 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 136 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 286 2 34 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 136 286 2 33 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 136 286 (accept_3_3 65 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 136 286 2 32 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 136 286 (Polychromatic418967fa.accept_19_6_3_1_1_2824 63 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 136 286 2 31 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 136 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 136 286 2 30 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 136 286 (accept_3_3 59 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 136 286 2 29 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 136 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 286 2 28 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 286 2 27 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 286 (accept_3_3 53 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 286 2 26 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 286 2 25 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 286 2 24 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 136 286 (accept_3_3 47 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 136 286 2 23 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 136 286 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 286 2 22 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 286 2 21 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 286 (accept_3_3 41 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 286 2 20 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 286 2 19 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 136 286 2 18 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 136 286 (accept_3_3 35 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 136 286 2 17 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 136 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 286 2 16 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 136 286 2 15 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 136 286 (accept_3_3 29 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 136 286 2 14 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 136 286 (Polychromatic418967fa.accept_20_7_16_6_1_7784 27 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 286 2 13 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 286 2 12 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 286 (accept_3_3 23 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 286 2 11 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 286 2 10 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 286 2 9 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 136 286 (accept_3_3 17 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 286 2 8 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 136 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 286 2 7 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 286 2 6 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 136 286 (accept_3_3 11 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 136 286 2 5 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 136 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 136 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 286 2 4 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 286 2 3 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 286 (accept_3_3 5 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  286 2 2 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 136 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 286 2 1 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 136 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 136 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 135 286 (allA_succ_of_accept 134 135 286 (accept_3_3 134 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 133 135 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 135 286 (Polychromatic418967fa.accept_16_4_7_14_1_3897 132
  135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 135 286 (accept_3_3 131
  135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 135 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 130 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 129 135 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 135 286 (accept_3_3 128 135 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 127 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 127 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 135 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 126 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 135 286 (accept_3_3 125 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  124 135 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 124 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 135 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 123 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 135 286 (accept_3_3 122 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 135 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 120 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 135 286 (accept_3_3 119 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  118 135 286 (Polychromatic418967fa.accept_25_18_10_11_1_17533 118 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 117 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 135 286 (accept_3_3 116 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 135 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 114 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 135 286 (accept_3_3 113 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 135 286 (Polychromatic418967fa.accept_20_12_15_6_1_9201 112 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 135 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 111 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 135 286 (accept_3_3 110 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3
  109 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 135 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 108 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 135 286 (accept_3_3 107 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 135 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 106 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 135 286 (accept_3_3 104 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 135 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 102 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 135 286 (accept_3_3 101 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 135 286 (Polychromatic418967fa.accept_16_4_7_14_1_3897 100 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 135 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 135 286 (accept_3_3 98 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 286
  (Polychromatic418967fa.accept_17_11_16_14_1_6760 96 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 135 286 (accept_3_3 95 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 135 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 94 135 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 135 286 (accept_3_3 92 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 91
  135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 90 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 135 286 (accept_3_3 89 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 135 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 135 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 286 (accept_3_3 86 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 84 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 135 286 (accept_3_3 83 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 135 286 (Polychromatic418967fa.accept_19_6_2_1_1_4051 82 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 286 (accept_3_3 80 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 135 286 (accept_3_3 77 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 135 286 (Polychromatic418967fa.accept_17_8_16_14_1_4261 76 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 135 286 (Polychromatic418967fa.accept_19_18_2_1_1_5375 75 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 286 (accept_3_3 74 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 286
  (Polychromatic418967fa.accept_19_15_2_1_1_2822 72 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 135 286 (accept_3_3 71 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 135 286 (Polychromatic418967fa.accept_17_2_16_14_1_2116 70 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 286 (accept_3_3 68 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 135 286 (accept_3_3 65 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 135 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 135 286 (Polychromatic418967fa.accept_16_15_7_14_1_2883 63 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 286 (accept_3_3 62 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 135 286 (accept_3_3 59 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 135 286 (Polychromatic418967fa.accept_16_10_7_14_1_2882 58 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 286 (accept_3_3 56 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 135 286 (accept_3_3 53 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 135 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 135 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 286 (accept_3_3 50 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 286
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 286 (accept_3_3 47 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 135 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 286 (accept_3_3 44 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 286 (accept_3_3 41 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 135 286 (Polychromatic418967fa.accept_25_15_10_11_1_17562 40 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 286 (accept_3_3 38 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 135 286 (accept_3_3 35 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 135 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 286 (accept_3_3 32 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 286 (accept_3_3 29 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 286 (Polychromatic418967fa.accept_17_11_16_14_1_6760 28 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 286 (Polychromatic418967fa.accept_19_8_2_1_1_4053 27 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 286 (accept_3_3 26 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 286 (accept_3_3 23 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 286 (accept_3_3 20 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 286 (accept_3_3 17 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 286 (Polychromatic418967fa.accept_21_16_9_13_1_4127 16 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 286 (accept_3_3 14 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 286
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 286 (accept_3_3 11 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 135 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 286 (accept_3_3 8 135 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 286 (accept_3_3 5 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 135 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 286 (accept_3_3 2 135 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 134 286 (allA_of_3_1 134 134 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 133 286
  (allA_succ_of_accept 132 133 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 132 133 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 133 286 (accept_3_3 131 133 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 130 133 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 130 133 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 129 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 133 286 (accept_3_3 128 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 127 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 133 286 (Polychromatic418967fa.accept_24_6_13_22_1_7332 126 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 133 286 (accept_3_3 125 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 133 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 124 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 123 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 133 286 (accept_3_3 122 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 133 286 (Polychromatic418967fa.accept_16_9_5_14_1_6126 121 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 120 133 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 120 133 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 133 286 (accept_3_3 119 133 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 133 286 (Polychromatic418967fa.accept_10_8_3_6_1_685
  118 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 133 286 (accept_3_3 116 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 115 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 133 286 (Polychromatic418967fa.accept_21_9_7_13_1_8742 114 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 133 286 (accept_3_3 113 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 133 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 112 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 133 286 (accept_3_3 110 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 133 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 109 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 133 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 108 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 133 286 (accept_3_3 107 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 133 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 106 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 133 286 (accept_3_3 104 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 133 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 102 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 286 (accept_3_3 101 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 100 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 133 286 (accept_3_3 98 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 133 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 97 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 133 286 (Polychromatic418967fa.accept_25_21_8_11_1_17561 96 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 286 (accept_3_3 95 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 286 (Polychromatic418967fa.accept_18_4_7_16_1_2307 94 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 286 (accept_3_3 92 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 286 (Polychromatic418967fa.accept_16_10_5_14_1_6173 90 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 286 (accept_3_3 89 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 133 286 (accept_3_3 86 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 133 286 (Polychromatic418967fa.accept_14_1_7_6_1_3604 85 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 133 286 (Polychromatic418967fa.accept_23_15_18_10_1_17560 84 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 286 (accept_3_3 83 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 286 (Polychromatic418967fa.accept_21_19_7_13_1_7189 82 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 286 (accept_3_3 80 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 78 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 286 (accept_3_3 77 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 286 (accept_3_3 74 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 286 (Polychromatic418967fa.accept_16_9_5_14_1_6126 73 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 72 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 286 (accept_3_3 71 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 286 (accept_3_3 68 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 286 (Polychromatic418967fa.accept_25_16_8_11_1_15957 66 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 286 (accept_3_3 65 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 286 (accept_3_3 62 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 286 (Polychromatic418967fa.accept_21_19_7_13_1_7189 61 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 286 (Polychromatic418967fa.accept_21_18_7_13_1_8801 60 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 286 (accept_3_3 59 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 286 (accept_3_3 56 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 286 (Polychromatic418967fa.accept_23_8_18_10_1_9658 54 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 286 (accept_3_3 53 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 286 (accept_3_3 50 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 286 (accept_3_3 47 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 286 (Polychromatic418967fa.accept_21_4_7_13_1_8757 46 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 286 (accept_3_3 44 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 286 (accept_3_3 41 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 286 (accept_3_3 38 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 286 (accept_3_3 35 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 286 (Polychromatic418967fa.accept_25_9_8_11_1_17559 34 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 286 (accept_3_3 32 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 286 (Polychromatic418967fa.accept_21_9_7_13_1_8742 30 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 286 (accept_3_3 29 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 286 (accept_3_3 26 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 286 (Polychromatic418967fa.accept_25_24_8_11_1_17558 24 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 286 (accept_3_3 23 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 286 (accept_3_3 20 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 286 (accept_3_3 17 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 286 (accept_3_3 14 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 286 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 286 (accept_3_3 11 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 133
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 286 (accept_3_3 8 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 286 (Polychromatic418967fa.accept_21_6_7_13_1_7199 6 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 286 (accept_3_3 5 133 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 133 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 286 (accept_3_3 2 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 286 (Polychromatic418967fa.accept_14_1_7_6_1_3604 1 133 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 132 286 (allA_succ_of_accept 131 132 286 (accept_3_3 131 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 132 286 2 65 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 132 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 129 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 132 286 2 64 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 132 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 127 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 132 286 2 63 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 132 286 (accept_3_3 125 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 132 286 2 62 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 132 286 (Polychromatic418967fa.accept_17_4_13_14_1_1139 123 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 132 286 2 61 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 121 132 286 11 11 12 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 120 132 286 2 60 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 132 286
  (accept_3_3 119 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 132 286 2 59 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 132 286
  (Polychromatic418967fa.accept_20_17_12_6_1_6171 117 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 132 286 2 58 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 132 286 (Polychromatic418967fa.accept_20_15_12_6_1_9199 115 132 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 132 286 2 57 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 132 286 (accept_3_3
  113 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 132 286 2 56 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 132 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 111 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 132 286 22 5 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 132 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 109 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 286 2 54 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 286 (accept_3_3 107 132 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 132 286 2 53 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 132 286
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 105 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 132 286 2 52 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 132 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 103 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 132 286 2 51 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 132 286 (accept_3_3 101 132 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 132 286 2 50 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 132 286 11 9 12 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 132 286 2 49 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 286
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 97 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 132 286 2 48 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 132 286 (accept_3_3 95 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 286 2 47 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 132 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 93 132 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 286 2 46 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 91 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 286 2 45 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 286 (accept_3_3 89 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 132 286 22 4 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 87 132 286 (Polychromatic418967fa.accept_16_7_4_14_1_2860 87 132 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 132 286 2 43 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 85
  132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 132 286 2 42 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 132 286 (accept_3_3 83
  132 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 286 2 41 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 286 2 40 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 79 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 132 286 2 39 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 132 286 11 7 12 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 132 286 2 38 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 286 2 37 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 132 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 132 286 2 36 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 132 286 (accept_3_3 71 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 286 2 35 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 286 (Polychromatic418967fa.accept_17_1_13_14_1_478
  69 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 132 286 2 34 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 286 22 3 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 132 286 (accept_3_3 65 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64
  132 286 2 32 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 132 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 63 132 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 132 286 2 31 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 286 2 30 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 286 (accept_3_3 59 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 286 2 29 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 132 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 132 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 132 286 2 28 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 132 286 11 5 12 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 132 286 2 27 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 132 286 (accept_3_3 53
  132 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 286 2 26 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 286 2 25 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 132 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 286 2 24 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 286 (accept_3_3 47 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 286 2 23 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 286 (Polychromatic418967fa.accept_19_7_18_1_1_1662
  45 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 286 22 2 6 13
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 132 286 2 21 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 132 286 (accept_3_3 41 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 286 2 20 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 132 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 286 2 19 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 286 2 18 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 286 (accept_3_3 35 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 286 2 17 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 132 286 11 3 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 286 2 16 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 132 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 286 2 15 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 286 (accept_3_3 29
  132 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 286 2 14 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 286
  (Polychromatic418967fa.accept_17_10_13_14_1_3094 27 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 132 286 2 13 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 132 286 (Polychromatic418967fa.accept_16_9_4_14_1_1878 25 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 286 2 12 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 286 (accept_3_3 23 132 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 286 22 1 6 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 286 2 10 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 132 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 132 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 286 2 9 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 286 (accept_3_3 17 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 286 2 8 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 286
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 15 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 286 2 7 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 132 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 286 2 6 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 132 286 11 1 12 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 132 286 2 5 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 286
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 286 2 4 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 286 (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 132 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 286 2 3 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 286 (accept_3_3 5 132 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 286 2 2 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 132 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 286 2 1 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 132 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 131 286 (allA_of_3_1 131 131 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 130 286
  (allA_succ_of_accept 129 130 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 129 130 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 130 286 2 64 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 130 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 127
  130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 130 286 2 63 65 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 130 286
  (accept_3_3 125 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 130 286 2 62 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 130 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 123 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 130 286 2 61 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 130 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 121 130 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 130 286 2 60 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 130 286 (accept_3_3 119 130 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 130 286 2 59 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 117 130 286 13 9 10 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 130 286 2 58 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 130 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 115 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 130 286 2 57 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 130 286 (accept_3_3 113 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 130 286 2 56 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 130 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 111 130 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 130 286 2 55 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 130 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 109 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 130 286 2 54 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 130 286 (accept_3_3 107 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 130 286 2 53 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 130 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 105 130 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 130 286 26 4 5 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 130 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 103 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 130 286 2 51 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 130 286 (accept_3_3 101 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 130 286 2 50 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 130 286 (Polychromatic418967fa.accept_15_9_10_1_1_1062 99 130 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 130 286 2 49 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 130 286
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 97 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 130 286 2 48 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 130 286 (accept_3_3 95 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 130 286 2 47 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 130 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 130 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 130 286 2 46 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 91 130 286 13 7 10 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 90 130 286 2 45 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 130 286 (accept_3_3 89
  130 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 130 286 2 44 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 130 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 130 286 2 43 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 130 286 (Polychromatic418967fa.accept_20_5_10_6_1_6166 85 130 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 130 286 2 42 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 130 286 (accept_3_3 83 130 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 130 286 2 41 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 130 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 130 286 2 40 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 130 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 130 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 130 286 26 3 5 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 130 286 (accept_3_3 77 130 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 130 286 2 38 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 130 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 75
  130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 130 286 2 37 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 130 286 2 36 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 130 286 (accept_3_3 71 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 286 2 35 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 130 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 286 2 34 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 286
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 130 286 2 33 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 130 286 13 5 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 130 286 2 32 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 130 286 (Polychromatic418967fa.accept_17_12_11_14_1_3120 63 130
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 286 2 31 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 286 2 30 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 286 (accept_3_3 59 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 286 2 29 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 130 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 286 2 28 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 130 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 130 286 2 27 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 130 286 (accept_3_3 53 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 130 286 26 2 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 130 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 130 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 286 2 25 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 286
  (Polychromatic418967fa.accept_20_9_10_6_1_16252 49 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 130 286 2 24 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 130 286 (accept_3_3 47 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 286 2 23 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 130 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 286 2 22 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 286
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 130 286 2 21 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 130 286 (accept_3_3 41 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 286 2 20 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 130 286 13 3 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 130 286 2 19 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 130 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 130 286 2 18 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 130 286 (accept_3_3 35
  130 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 130 286 2 17 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 130 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 130 286 2 16 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 130 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 130 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 286 2 15 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 286 (accept_3_3 29 130 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 130 286 2 14 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 130 286
  (Polychromatic418967fa.accept_19_8_16_1_1_11051 27 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 130 286 26 1 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 130 286 (Polychromatic418967fa.accept_17_8_11_14_1_6770 25 130 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 130 286 2 12 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 286 (accept_3_3 23
  130 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 286 2 11 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 130 286 2 10 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 130 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 130 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 130 286 2 9 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 130 286 (accept_3_3 17 130 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 130 286 2 8 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 130 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15
  130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 130 286 2 7 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 130 286 13 1 10 22
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 130 286 2 6 65
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 286
  (accept_3_3 11 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 286 2 5 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 286 2 4 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 130 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 286 2 3 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 286 (accept_3_3 5 130 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130 286 2 2 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 130 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 130 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 286 2 1 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 130 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 130
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 129 286 (allA_succ_of_accept 128 129 286 (accept_3_3 128 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 127 129 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 129 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 126 129
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 129 286 (accept_3_3 125 129
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 129 286
  (Polychromatic418967fa.accept_17_5_10_14_1_2083 124 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 123 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 129 286 (accept_3_3 122 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 129 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 129 286
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 120 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 129 286 (accept_3_3 119 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 129 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 118 129 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 129 286 (Polychromatic418967fa.accept_20_17_9_6_1_6219 117
  129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 129 286 (accept_3_3 116
  129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 115 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 129 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 114 129 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 129 286 (accept_3_3 113 129 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 129 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 112 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 111 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 129 286 (accept_3_3 110 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 129 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 108 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 129 286 (accept_3_3 107 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 129 286 (Polychromatic418967fa.accept_19_11_15_1_1_12391 106
  129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 129 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 105 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 129 286 (accept_3_3 104 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 103 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 129 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 286 (accept_3_3 101 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 100 129 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 129 286 (accept_3_3 98 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 129 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 96 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 286 (accept_3_3 95 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 93 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 129 286 (accept_3_3 92 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 129 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 90 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 286 (accept_3_3 89 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 88 129 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 129 286 (accept_3_3 86 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 129 286 (Polychromatic418967fa.accept_16_4_1_14_1_3908 84 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 286 (accept_3_3 83 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 129 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 129 286 (accept_3_3 80 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 129 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 78 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 286 (accept_3_3 77 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 129 286 (accept_3_3 74 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 129 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 286 (accept_3_3 71 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 286 (Polychromatic418967fa.accept_15_10_9_1_1_3688 70 129 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 129 286 (accept_3_3 68 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 129 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 286 (accept_3_3 65 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 129 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 129 286 (accept_3_3 62 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 129 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 286 (accept_3_3 59 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 286
  (Polychromatic418967fa.accept_20_17_9_6_1_6219 57 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 129 286 (accept_3_3 56 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 129 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 286 (accept_3_3 53 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 52 129
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 129 286 (accept_3_3 50 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 286 (Polychromatic418967fa.accept_21_6_3_13_1_2742 48 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 286 (accept_3_3 47 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 129 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 286
  (Polychromatic418967fa.accept_10_5_9_6_1_697 45 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 286 (accept_3_3 44 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 286 (accept_3_3 41 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 286 (accept_3_3 38 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 286 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 286 (accept_3_3 35 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 286 (Polychromatic418967fa.accept_20_14_9_6_1_3346 34 129
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 286 (accept_3_3 32 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 286 (accept_3_3 29 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 286 (accept_3_3 26 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 286 (accept_3_3 23 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 286 (accept_3_3 20 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 286 (accept_3_3 17 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 286 (accept_3_3 14 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 286 (Polychromatic418967fa.accept_21_12_3_13_1_7145 12 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 286 (accept_3_3 11 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 129 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 286 (accept_3_3 8 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 286 (accept_3_3 5 129 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 129 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 286 (accept_3_3 2 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 286 (allA_of_3_1 128 128 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 127 286
  (allA_succ_of_accept 126 127 286 (Polychromatic418967fa.accept_15_6_7_1_1_93 126 127 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 127 286 (accept_3_3 125 127 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 127 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 124 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 123 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 127 286 (accept_3_3 122 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 121 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 127 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 120 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 127 286 (accept_3_3 119 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 127 286 (Polychromatic418967fa.accept_17_16_8_14_1_6757 118
  127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 117 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 127 286 (accept_3_3 116 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 127 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 115 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 127 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 114 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 127 286 (accept_3_3 113 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 127 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 112 127
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 127 286 (accept_3_3 110 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 109 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 127 286 (Polychromatic418967fa.accept_17_6_8_14_1_6706 108 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 127 286 (accept_3_3 107 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 127 286 (Polychromatic418967fa.accept_16_10_15_14_1_1086 106
  127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 127 286 (accept_3_3 104 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 127 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 103 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 127 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 102 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 286 (accept_3_3 101 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 127 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 100 127
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 127 286 (accept_3_3 98 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 127 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 127 286 (accept_3_3 95 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 127 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 127 286 (accept_3_3 92 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 127 286 (Polychromatic418967fa.accept_10_1_7_6_1_91 91 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 127 286 (Polychromatic418967fa.accept_16_10_15_14_1_1086 90 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 286 (accept_3_3 89 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 88 127
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 127 286 (accept_3_3 86 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 286 (accept_3_3 83 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 286 (accept_3_3 80 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 286 (accept_3_3 77 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 286 (accept_3_3 74 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 286 (accept_3_3 71 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 70 127 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 286 (accept_3_3 68 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 286 (accept_3_3 65 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 286 (accept_3_3 62 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 286 (accept_3_3 59 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 286 (accept_3_3 56 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 286 (accept_3_3 53 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 286 (accept_3_3 50 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 286 (accept_3_3 47 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 286 (Polychromatic418967fa.accept_18_10_1_16_1_579 46 127 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 286 (accept_3_3 44 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 43 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 286 (accept_3_3 41 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 286 (accept_3_3 38 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 286 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 286 (accept_3_3 35 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 286 (Polychromatic418967fa.accept_25_9_2_11_1_17557 34 127 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 286 (accept_3_3 32 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 286 (accept_3_3 29 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 286 (accept_3_3 26 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 286 (accept_3_3 23 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 286 (accept_3_3 20 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 286 (Polychromatic418967fa.accept_19_18_13_1_1_9735 18 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 286 (accept_3_3 17 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 127 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 286 (accept_3_3 14 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 286 (accept_3_3 11 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 127 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 286 (accept_3_3 8 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 286 (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 286 (accept_3_3 5 127 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 286 (accept_3_3 2 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 126 286 (allA_succ_of_accept 125 126 286 (accept_3_3 125 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 126 286 2 62 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 123 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 126 286 2 61 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 126 286
  (Polychromatic418967fa.accept_19_7_12_1_1_6830 121 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 120 126 286 2 60 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 119 126 286 (accept_3_3 119 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 126 286 2 59 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 117 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 126 286 2 58 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 126 286
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 115 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 126 286 2 57 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 126 286 (accept_3_3 113 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 126 286 2 56 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 111 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 126 286 2 55 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 126 286
  (Polychromatic418967fa.accept_23_17_11_10_1_11257 109 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 108 126 286 2 54 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 107 126 286 (accept_3_3 107 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 126 286 2 53 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 105 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 126 286 2 52 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 126 286
  (Polychromatic418967fa.accept_19_8_12_1_1_11084 103 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 126 286 2 51 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 126 286 (accept_3_3 101 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 126 286 2 50 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 99 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 126 286 2 49 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 126 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 97 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 286 2 48 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 286 (accept_3_3 95 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 126 286 2 47 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 93 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 126 286 2 46 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 126 286
  (Polychromatic418967fa.accept_17_6_7_14_1_6704 91 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 286 2 45 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 286 (accept_3_3 89 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 126 286 2 44 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 87 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 126 286 2 43 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 286
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 85 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 286 2 42 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 286 (accept_3_3 83 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 126 286 2 41 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 81 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 126 286 2 40 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 286
  (Polychromatic418967fa.accept_27_25_18_16_1_15796 79 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 126 286 2 39 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 126 286 (accept_3_3 77 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 126 286 2 38 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 75 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 126 286 2 37 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 286
  (Polychromatic418967fa.accept_24_1_6_22_1_11014 73 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 126 286 2 36 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 126 286 (accept_3_3 71 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 126 286 2 35 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 126 286 2 34 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 67 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 286 2 33 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 286 (accept_3_3 65 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 126 286 2 32 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 126 286 2 31 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 286
  (Polychromatic418967fa.accept_17_10_7_14_1_4244 61 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 126 286 2 30 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 126 286 (accept_3_3 59 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 126 286 2 29 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 126 286 2 28 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 286
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 286 2 27 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 286 (accept_3_3 53 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 126 286 2 26 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 286 2 25 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 286
  (Polychromatic418967fa.accept_19_11_12_1_1_11049 49 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 126 286 2 24 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 126 286 (accept_3_3 47 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 286 2 23 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 286 2 22 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 286
  (Polychromatic418967fa.accept_19_5_12_1_1_2817 43 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 286 2 21 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 286 (accept_3_3 41 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 286 2 20 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 286 2 19 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 286 2 18 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 286 (accept_3_3 35 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 286 2 17 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 286 2 16 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 286
  (Polychromatic418967fa.accept_30_1_6_16_1_17556 31 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 126 286 2 15 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 126 286 (accept_3_3 29 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 286 2 14 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 286 2 13 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 286
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 286 2 12 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 286 (accept_3_3 23 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 286 2 11 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 286 2 10 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 286
  (Polychromatic418967fa.accept_25_19_1_11_1_17555 19 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 126 286 2 9 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 126 286 (accept_3_3 17 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 126 286 2 8 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 286 2 7 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 286
  (Polychromatic418967fa.accept_19_13_12_1_1_3993 13 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 286 2 6 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 286 (accept_3_3 11 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 286 2 5 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 126 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 126 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 286 2 4 63 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 286 2 3 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 286 (accept_3_3 5 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  286 2 2 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 126 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 286 2 1 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 126 286 (Polychromatic418967fa.accept_23_1_11_10_1_17554 1 126 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 286 (allA_of_3_1 125 125 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 124 286
  (allA_succ_of_accept 123 124 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 123 124 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 124 286 2 61 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 124 286 (Polychromatic418967fa.accept_12_1_4_10_1_209
  121 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 124 286 2 60 62 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 124 286
  (accept_3_3 119 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 124 286 2 59 62 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 124 286
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 117 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 124 286 2 58 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 124 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 115 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 124 286 2 57 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 124 286 (accept_3_3 113 124 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 124 286 2 56 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 124 286
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 111 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 124 286 2 55 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 124 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 109 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 124 286 2 54 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 124 286 (accept_3_3 107 124 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 124 286 2 53 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 124 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 105 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 124 286 2 52 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 124 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 103 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 124 286 2 51 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 124 286 (accept_3_3 101 124 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 124 286 2 50 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 124 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 124 286 2 49 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 124 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 97 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 124 286 2 48 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 124 286 (accept_3_3 95 124 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 124 286 2 47 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 124 286
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 93 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 124 286 2 46 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 124 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 91 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 124 286 2 45 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 124 286 (accept_3_3 89 124 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 124 286 2 44 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 124 286
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 87 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 124 286 2 43 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 124 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 124 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 124 286 2 42 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 124 286 (accept_3_3 83 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 124 286 2 41 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 124 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 81
  124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 124 286 2 40 62 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 124 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 124 286 2 39 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 124 286 (accept_3_3 77 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 124 286 2 38 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 124 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 75 124 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 286 2 37 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 286 2 36 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 286 (accept_3_3 71 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 286 2 35 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 69 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 286 2 34 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 286 2 33 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 286 (accept_3_3 65 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 286 2 32 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 286 2 31 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 286 2 30 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 286 (accept_3_3 59 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 286 2 29 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 124 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 286 2 28 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 286 2 27 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 286 (accept_3_3 53 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 286 2 26 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 286 (Polychromatic418967fa.accept_19_13_10_1_1_8236 51 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 286 2 25 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 286 2 24 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 286 (accept_3_3 47 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 286 2 23 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 124 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 286 2 22 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 286 2 21 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 286 (accept_3_3 41 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 286 2 20 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 124 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 286 2 19 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 286 2 18 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 124 286 (accept_3_3 35 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 124 286 2 17 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 124 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 33 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 286 2 16 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 286 2 15 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 286 (accept_3_3 29 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 286 2 14 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 286 2 13 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 286 2 12 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 286 (accept_3_3 23 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 286 2 11 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 286 (Polychromatic418967fa.accept_25_21_24_11_1_12466 21 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 286 2 10 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 286 2 9 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 124 286 (accept_3_3 17 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 124 286 2 8 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 124 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 124 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 286 2 7 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 286 2 6 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 124 286 (accept_3_3 11 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 124 286 2 5 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 124 286 (Polychromatic418967fa.accept_17_9_5_14_1_4277 9 124 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 286 2 4 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 124 286 2 3 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 286 (accept_3_3 5 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  286 2 2 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 124 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 286 2 1 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 124 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 124 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_286_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


