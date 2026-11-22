-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch181_Segment000
-- name    : Polychromatic418967fa_Branch181_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:27:56.305418+00:00
-- url     : https://prove2.me/theorems/30781cbd-834f-4f37-8b65-8cb6c45d1783
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

def Polychromatic418967fa.branch_181_segment_000 : allB 144 181 :=
  allB_succ' 39 143 181 (Eq.refl Bool.true) (allA_of_3_1 39 143 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  40 142 181 (Eq.refl Bool.true) (allA_succ_of_accept 39 142 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 142 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 181 (accept_3_3 38 142 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 181
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 142 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 142 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 142 181 (accept_3_3 35 142 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 142 181 (Polychromatic418967fa.accept_19_15_9_10_1_4615 34 142 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 142 181 (accept_3_3 32 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 142 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 142 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 142 181 (accept_3_3 29 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 142 181 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 142 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 142 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 142 181 (accept_3_3 26 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 142 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 142 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 142 181 (accept_3_3 23 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 142 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 142 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 142 181 (accept_3_3 20 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 142 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 142 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 142 181 (accept_3_3 17 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 142 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 142 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 142 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 142 181 (accept_3_3 14 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 142 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 142 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 142 181 (accept_3_3 11 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 142 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 142 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 142 181 (accept_3_3 8 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  142 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 142 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 181 (accept_3_3 5 142 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 142 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 142 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 142 181 (accept_3_3 2 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  142 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 142 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 142 181)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 141 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 141 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 141 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 181 (accept_3_3 38 141 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 181 (Polychromatic418967fa.accept_7_2_1_6_1_173
  37 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 181
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 181 (accept_3_3 35 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 141 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 141 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 181 (accept_3_3 32 141 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 181 (Polychromatic418967fa.accept_9_4_6_1_1_393
  31 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 181 (accept_3_3 29 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 141 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 181 (accept_3_3 26 141 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 141 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 181
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 181 (accept_3_3 23 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 181 (accept_3_3 20 141 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 141 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 181
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 181 (accept_3_3 17 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 141 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 181 (accept_3_3 14 141 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 141 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 181 (accept_3_3 11 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 181 (accept_3_3 8 141 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 141 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 181
  (Polychromatic418967fa.accept_17_6_5_11_1_4073 6 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 181 (accept_3_3 5 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 141 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 181 (accept_3_3 2 141 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 181 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 141 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 181)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 140 181 (Eq.refl Bool.true) (allA_of_3_1 42 140 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 43 139 181 (Eq.refl Bool.true) (allA_succ_of_accept 42 139 181 (Polychromatic418967fa.accept_4_2_3_1_1_2
  42 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 181 (accept_3_3 41
  139 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 181
  (Polychromatic418967fa.accept_16_8_11_5_1_3319 40 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 139 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 139 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 181 (accept_3_3 38 139 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 139 181 (Polychromatic418967fa.accept_27_10_4_19_1_10434 37 139 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 181
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 139 181 (accept_3_3 35 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 139 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 139 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 139 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 181 (accept_3_3 32 139 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 181 (Polychromatic418967fa.accept_11_9_7_5_1_749
  31 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 181 (accept_3_3 29 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 181 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 181 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 139 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 181 (accept_3_3 26 139 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 139 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 181 (accept_3_3 23 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 139 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 181 (accept_3_3 20 139 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 181 (Polychromatic418967fa.accept_17_2_3_11_1_2919 19 139 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 181 (accept_3_3 17 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 139 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 181 (accept_3_3 14 139 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 181 (Polychromatic418967fa.accept_19_13_6_10_1_7395 13 139 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 181 (accept_3_3 11 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 181 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 139 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 181 (accept_3_3 8 139 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 139 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 181 (accept_3_3 5 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 181 (Polychromatic418967fa.accept_19_4_6_10_1_7396 4 139 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 139 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 181 (accept_3_3 2 139 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 181 (Polychromatic418967fa.accept_19_1_6_10_1_3366 1 139 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 181)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 138 181 (Eq.refl Bool.true) (allA_succ_of_accept 43 138 181 (Polychromatic418967fa.accept_4_3_2_1_1_50
  43 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 138 181 (accept_3_3 41 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 138 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 138 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 181 (accept_3_3 38 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 181 (Polychromatic418967fa.accept_17_3_2_11_1_1895 37 138 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 138 181 (accept_3_3 35 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 138 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 138 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 181 (accept_3_3 32 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 138 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 181
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 138 181 (accept_3_3 29 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 138 181 (Polychromatic418967fa.accept_15_13_3_1_1_3740 28 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 138 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 181 (accept_3_3 26 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 138 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 138 181 (accept_3_3 23 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 138 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 138 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 138 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 181 (accept_3_3 20 138 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 138 181 (accept_3_3 17 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 138 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 138 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 181 (accept_3_3 14 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 138 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 181
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 138 181 (accept_3_3 11 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 138 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 138 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 181 (accept_3_3 8 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 138 181 (accept_3_3 5 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  138 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 138 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 138 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 181 (accept_3_3 2 138 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 138 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 181))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 137 181 (Eq.refl Bool.true) (allA_of_3_1 45 137 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 136 181 (Eq.refl Bool.true) (allA_succ_of_accept 45 136 181 (Polychromatic418967fa.accept_6_3_4_1_1_8
  45 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 181 (accept_3_3 44
  136 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 181
  (Polychromatic418967fa.accept_11_10_4_5_1_359 43 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 136 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 136 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 136 181 (accept_3_3 41 136 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 136 181 (Polychromatic418967fa.accept_22_18_4_5_1_10433 40 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 136 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 136 181 (accept_3_3 38 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 136 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 136 181 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 136 181 (accept_3_3 35 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 136 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 136
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 136 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 136 181 (accept_3_3 32 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 136 181 (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 136 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 136 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 136 181 (accept_3_3 29 136 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 136 181 (Polychromatic418967fa.accept_13_2_6_12_1_1334 28 136 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 136 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 136 181 (accept_3_3 26 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 136 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 136 181 (Polychromatic418967fa.accept_19_5_3_10_1_4641 24 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 136 181 (accept_3_3 23 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 136 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 136
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 136 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 136 181 (accept_3_3 20 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 136 181 (Polychromatic418967fa.accept_16_3_8_5_1_6790 19 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 136 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 136 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 181 (accept_3_3 17 136 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 136 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 136 181 (accept_3_3 14 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 136 181 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 136 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 181 (accept_3_3 11 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 181 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 136
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 181 (accept_3_3 8 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 181 (Polychromatic418967fa.accept_20_6_16_1_1_7262 6 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 181 (accept_3_3 5 136 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 136 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 181 (accept_3_3 2 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 181 (Polychromatic418967fa.accept_19_1_3_10_1_8917 1 136 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136 181)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 135 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 135 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 135 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 135 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 181 (accept_3_3 44 135 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 43
  135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 181 (accept_3_3 41 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 135 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 135 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 135 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 181 (accept_3_3 38 135 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 181 (Polychromatic418967fa.accept_19_18_2_10_1_10412 37 135 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 135 181 (accept_3_3 35 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 135 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 135 181 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 135 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 181 (accept_3_3 32 135 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 135 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 181 (accept_3_3 29 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 135 181 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 135 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 181 (accept_3_3 26 135 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 135 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 181 (accept_3_3 23 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 181 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 135 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 181 (accept_3_3 20 135 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 135
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 181 (accept_3_3 17 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 135 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 181 (accept_3_3 14 135 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 181 (Polychromatic418967fa.accept_19_13_2_10_1_7416 13 135 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 181
  (Polychromatic418967fa.accept_16_12_7_5_1_1412 12 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 181 (accept_3_3 11 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 135 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 135 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 135 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 181 (accept_3_3 8 135 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 181 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 135 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 181 (accept_3_3 5 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 181 (accept_3_3 2 135 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 135 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 181)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 134 181 (Eq.refl Bool.true) (allA_of_3_1 48 134 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 133 181 (Eq.refl Bool.true) (allA_succ_of_accept 48 133 181 (Polychromatic418967fa.accept_9_3_7_1_1_143
  48 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 181 (accept_3_3 47
  133 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 181
  (Polychromatic418967fa.accept_17_12_14_11_1_998 46 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 181 (Polychromatic418967fa.accept_25_20_8_6_1_10432 45 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 181 (accept_3_3 44 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 181 (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 133
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 181 (accept_3_3 41 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 133 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 181 (accept_3_3 38 133 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 181 (Polychromatic418967fa.accept_17_3_14_11_1_5243 37 133 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 181
  (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 133 181 (accept_3_3 35 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 133 181 (Polychromatic418967fa.accept_14_6_7_13_1_3158 34 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 133 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 133 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 181 (accept_3_3 32 133 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 181 (accept_3_3 29 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 181 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 181 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 181 (accept_3_3 26 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 133
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 181 (accept_3_3 23 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 133 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 181 (accept_3_3 20 133 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 181 (Polychromatic418967fa.accept_21_19_7_13_1_7189 19 133 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 181
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 181 (accept_3_3 17 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 181 (Polychromatic418967fa.accept_17_16_14_11_1_7836 16 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 181 (accept_3_3 14 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 133 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 181 (accept_3_3 11 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 181 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 181 (accept_3_3 8 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 181 (Polychromatic418967fa.accept_27_7_25_19_1_10431 7 133
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 181 (accept_3_3 5 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 133 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 133 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 181 (accept_3_3 2 133 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 181 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 133 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 181)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 132 181 (Eq.refl Bool.true) (allA_succ_of_accept 49 132 181 (Polychromatic418967fa.accept_8_1_4_5_1_48
  49 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 132 181 (accept_3_3 47 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 132 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 132 181 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 181 (accept_3_3 44 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 132 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 181
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 132 181 (accept_3_3 41 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 132 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 132 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 181 (accept_3_3 38 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 181 (Polychromatic418967fa.accept_21_16_6_13_1_10430 37 132 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 181
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 132 181 (accept_3_3 35 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 132 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 132 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 181 (accept_3_3 32 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 132 181 (accept_3_3 29 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 132 181 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 132 181 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 181 (accept_3_3 26 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 132 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 181
  (Polychromatic418967fa.accept_16_8_4_5_1_4379 24 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 132 181 (accept_3_3 23 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 132 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 132 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 181 (accept_3_3 20 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 181 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 181
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 132 181 (accept_3_3 17 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 132 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 132 181 (Polychromatic418967fa.accept_16_15_4_5_1_1411 15 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 181 (accept_3_3 14 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 132 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 132 181 (accept_3_3 11 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 132 181 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 132 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 181 (accept_3_3 8 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 181
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 132 181 (accept_3_3 5 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  132 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 132 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 132 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 181 (accept_3_3 2 132 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 132 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  181)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 131 181 (Eq.refl Bool.true) (allA_of_3_1 51 131
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 130 181 (Eq.refl Bool.true) (allA_succ_of_accept 51 130
  181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 130 181 (accept_3_3 50 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 130 181 (Polychromatic418967fa.accept_20_9_10_1_1_192 49 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 130 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 181 (accept_3_3 47 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 130 181 (Polychromatic418967fa.accept_19_8_16_10_1_7484 46 130 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 130 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 130 181 (accept_3_3 44 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 130 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 130 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 130 181 (accept_3_3 41 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 130 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 130 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 130 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 130 181 (accept_3_3 38 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 130 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 130 181 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 130 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 130 181 (accept_3_3 35 130 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 130 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 130 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 130 181 (accept_3_3 32 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 130 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 130 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 181 (accept_3_3 29 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 130 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 181 (accept_3_3 26 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 130 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 130 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 181 (accept_3_3 23 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 130 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 181 (accept_3_3 20 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 181 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 130 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 181 (accept_3_3 17 130 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 130 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 181 (accept_3_3 14 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 181 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 181 (accept_3_3 11 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 130 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 181 (accept_3_3 8 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 181 (accept_3_3 5 130 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 130 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 181 (accept_3_3 2 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 181 (Polychromatic418967fa.accept_19_1_16_10_1_6026 1 130 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130 181)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 129 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 129 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 51
  129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 181 (accept_3_3 50
  129 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 181
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 129 181 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 181 (accept_3_3 47 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 129 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 181 (Polychromatic418967fa.accept_10_5_9_1_1_187
  45 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 181 (accept_3_3 44
  129 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 181
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 129 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 181 (accept_3_3 41 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 129 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 181 (Polychromatic418967fa.accept_7_4_3_6_1_340
  39 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 181 (accept_3_3 38
  129 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 129 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 181 (accept_3_3 35 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 129 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 181 (Polychromatic418967fa.accept_9_6_3_1_1_155
  33 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 181 (accept_3_3 32
  129 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 181
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 129 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 181 (accept_3_3 29 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 129 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 181 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 181 (accept_3_3 26
  129 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 129 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 181 (accept_3_3 23 129 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 129 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 181 (Polychromatic418967fa.accept_15_6_9_1_1_1823
  21 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 181 (accept_3_3 20
  129 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 181
  (Polychromatic418967fa.accept_25_19_4_6_1_10429 19 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 181 (accept_3_3 17 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 181 (accept_3_3 14 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 181 (accept_3_3 11 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 129 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 181 (accept_3_3 8 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 181 (accept_3_3 5 129 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 181
  (Polychromatic418967fa.accept_11_3_8_5_1_336 3 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 181 (accept_3_3 2 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 181 (Polychromatic418967fa.accept_17_1_10_11_1_2943 1 129 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 181))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 128 181 (Eq.refl
  Bool.true) (allA_of_3_1 54 128 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 127 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 127 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 127 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 181 (accept_3_3 53 127 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 127 181 (Polychromatic418967fa.accept_16_4_15_5_1_5537 52 127 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 181 (accept_3_3 50 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 181 (Polychromatic418967fa.accept_14_7_1_13_1_357 49 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 181 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 127 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 181 (accept_3_3 47 127 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 127 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 181
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 181 (accept_3_3 44 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 181 (accept_3_3 41 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 127 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 181
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 181 (accept_3_3 38 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 181 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 127 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 181 (accept_3_3 35 127 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 127 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 181 (accept_3_3 32 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 181 (Polychromatic418967fa.accept_17_14_8_11_1_4052 31 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 181 (accept_3_3 29 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 181 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 127 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 181
  (Polychromatic418967fa.accept_43_27_41_9_1_10428 27 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 127 181 (accept_3_3 26 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 127 181 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 127 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 181 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 127
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 181 (accept_3_3 23 127
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 181 (Polychromatic418967fa.accept_4_2_3_1_1_2
  22 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 181
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 181 (accept_3_3 20 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 181 (accept_3_3 17 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 127 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 181
  (Polychromatic418967fa.accept_13_2_10_12_1_757 15 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 181 (accept_3_3 14 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 181 (Polychromatic418967fa.accept_25_13_2_6_1_10427 13 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 181 (accept_3_3 11 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 181 (accept_3_3 8 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 181 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 181 (accept_3_3 5 127 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 181 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 127 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 181
  (Polychromatic418967fa.accept_19_3_13_10_1_7461 3 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 181 (accept_3_3 2 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 127 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 181))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 126 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 126 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 126 181 (Polychromatic418967fa.accept_15_9_6_1_1_493
  54 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 126 181 (accept_3_3 53
  126 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 181
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 126 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 126 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 181 (accept_3_3 50 126 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 126 181 (Polychromatic418967fa.accept_13_10_9_12_1_2814 49 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 126 181
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 126 181 (accept_3_3 47 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 126 181 (Polychromatic418967fa.accept_19_8_12_10_1_9002 46 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 126 181 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 126 181 (accept_3_3 44 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 126 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 126 181
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 126 181 (accept_3_3 41 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 126 181 (Polychromatic418967fa.accept_15_10_6_1_1_3707 40 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 126 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 181 (accept_3_3 38 126 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 126 181
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 126 181 (accept_3_3 35 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 126 181 (Polychromatic418967fa.accept_13_8_9_12_1_2813 34 126 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 181 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 126
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 181 (accept_3_3 32 126
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 126 181 (Polychromatic418967fa.accept_17_13_7_11_1_3985 30 126 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 181 (accept_3_3 29 126 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 181 (Polychromatic418967fa.accept_19_9_12_10_1_10393 28 126 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 126 181 (accept_3_3 26 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 126 181 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 126 181 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 181 (accept_3_3 23 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 126
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 181
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 126 181 (accept_3_3 20 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 126 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 126 181 (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 181 (accept_3_3 17 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 181 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 126
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 126 181 (accept_3_3 14 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 126 181 (Polychromatic418967fa.accept_17_13_7_11_1_3985 13 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 126 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 181 (accept_3_3 11 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 181 (Polychromatic418967fa.accept_13_10_9_12_1_2814 10 126
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 181
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 126 181 (accept_3_3 8 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  126 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 126 181 (Polychromatic418967fa.accept_19_6_12_10_1_4683 6 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 181 (accept_3_3 5 126 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 181 (Polychromatic418967fa.accept_23_4_11_20_1_10426 4 126
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 126 181 (accept_3_3 2 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  126 181 (Polychromatic418967fa.accept_17_1_7_11_1_2892 1 126 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 126 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 125 181 (Eq.refl
  Bool.true) (allA_of_3_1 57 125 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 124 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 124 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 124 181 (accept_3_3 56 124 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 124 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 124 181
  (Polychromatic418967fa.accept_23_8_9_20_1_5177 54 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 124 181 (accept_3_3 53 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 124 181 (Polychromatic418967fa.accept_11_8_3_5_1_355 52 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 124 181 (accept_3_3 50 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 124 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 124 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 124 181 (accept_3_3 47 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 124 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 181 (accept_3_3 44 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 124 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 124 181 (accept_3_3 41 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 124 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 124 181 (accept_3_3 38 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 124 181 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 124 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 124 181 (accept_3_3 35 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 124 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 124 181 (accept_3_3 32 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 124 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 124 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 124 181 (accept_3_3 29 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 124 181 (Polychromatic418967fa.accept_18_10_16_1_1_1534 28 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 181 (accept_3_3 26 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 124 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 124 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 124 181 (accept_3_3 23 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 124 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 181 (accept_3_3 20 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 124 181 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 124 181 (accept_3_3 17 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 124 181 (Polychromatic418967fa.accept_17_16_5_11_1_7830 16 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 181 (accept_3_3 14 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 124 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 124 181 (accept_3_3 11 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 124 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 181 (accept_3_3 8 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 124 181 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 124 181 (accept_3_3 5 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  124 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 124 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 124 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 181 (accept_3_3 2 124 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 124 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 123 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 123 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 123 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 181 (accept_3_3 56 123 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 181
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 55 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 123 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 181 (accept_3_3 53 123 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 123 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 181 (Polychromatic418967fa.accept_7_2_4_6_1_166
  51 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 181 (accept_3_3 50
  123 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 181
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 123 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 123 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 181 (accept_3_3 47 123 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 181 (Polychromatic418967fa.accept_7_3_4_6_1_329
  45 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 181 (accept_3_3 44
  123 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 181
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 123 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 181 (accept_3_3 41 123 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 123 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 39
  123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 181 (accept_3_3 38
  123 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 123 181 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 181 (accept_3_3 35 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 123 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 123 181 (accept_3_3 32 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 123 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 181 (accept_3_3 29 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 181
  (Polychromatic418967fa.accept_17_10_4_11_1_4047 27 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 181 (accept_3_3 26 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 123 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 123 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 181 (accept_3_3 23 123 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 181 (accept_3_3 20 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 181 (accept_3_3 17 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 181
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 181 (accept_3_3 14 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 181 (accept_3_3 11 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 181 (accept_3_3 8 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 181 (accept_3_3 5 123 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 181 (accept_3_3 2 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 181 (Polychromatic418967fa.accept_19_1_9_10_1_10391 1 123 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 122 181
  (Eq.refl Bool.true) (allA_of_3_1 60 122 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 121 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 60 121 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 181 (accept_3_3 59 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 181 (Polychromatic418967fa.accept_19_1_7_10_1_8926 58 121 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 181 (accept_3_3 56 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 181 (Polychromatic418967fa.accept_13_3_4_12_1_36 55 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 181 (Polychromatic418967fa.accept_13_2_4_12_1_745 54 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 181 (accept_3_3 53 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 121 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 181 (accept_3_3 50 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 181 (Polychromatic418967fa.accept_16_1_9_5_1_5443 49 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 181 (accept_3_3 47 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 181 (accept_3_3 44 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 181 (accept_3_3 41 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 181 (Polychromatic418967fa.accept_21_19_16_13_1_4099 40 121 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 181 (accept_3_3 38 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 181 (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 181 (accept_3_3 35 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 181 (accept_3_3 32 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 181 (accept_3_3 29 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 181
  (Polychromatic418967fa.accept_16_11_9_5_1_4412 27 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 181 (accept_3_3 26 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 181 (accept_3_3 23 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 181 (accept_3_3 20 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 181 (Polychromatic418967fa.accept_21_19_16_13_1_4099 19 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 181 (accept_3_3 17 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 121 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 181 (accept_3_3 14 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 181 (Polychromatic418967fa.accept_16_13_9_5_1_3302 13 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 181 (accept_3_3 11 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 181
  (Polychromatic418967fa.accept_17_9_2_11_1_4042 9 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 181 (accept_3_3 8 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 181 (accept_3_3 5 121 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 121 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 181 (accept_3_3 2 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 121 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 120 181
  (Eq.refl Bool.true) (allA_succ_of_accept 61 120 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 120 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 120 181 (accept_3_3 59 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 120 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 120 181 (Polychromatic418967fa.accept_18_3_12_1_1_3787 57 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 181 (accept_3_3 56 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 181 (Polychromatic418967fa.accept_26_3_16_25_1_10425 55
  120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 120 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 120 181 (accept_3_3 53 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 120 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 120 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 120 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 181 (accept_3_3 50 120 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 181
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 120 181 (accept_3_3 47 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 120 181 (Polychromatic418967fa.accept_22_2_10_5_1_10424 46 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 120 181 (Polychromatic418967fa.accept_16_13_8_5_1_3298 45 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 181 (accept_3_3 44 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 120 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 120 181 (accept_3_3 41 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 120 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 120 181 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 181 (accept_3_3 38 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 120 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 181
  (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 120 181 (accept_3_3 35 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 120 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 120 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 120 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 181 (accept_3_3 32 120 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 120 181 (accept_3_3 29 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 120 181 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 120 181 (Polychromatic418967fa.accept_16_11_8_5_1_4366 27 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 181 (accept_3_3 26 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 120 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 181 (accept_3_3 23 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 120 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 181 (Polychromatic418967fa.accept_14_7_8_13_1_3161 21 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 181 (accept_3_3 20 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 120 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 181
  (Polychromatic418967fa.accept_21_18_15_13_1_4130 18 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 181 (accept_3_3 17 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 120 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 120 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 181 (accept_3_3 14 120 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 181 (Polychromatic418967fa.accept_9_4_3_1_1_154
  13 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 181 (accept_3_3 11 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 120 181 (Polychromatic418967fa.accept_17_10_1_11_1_2900 10 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 120 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 181 (accept_3_3 8 120 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 120 181 (accept_3_3 5 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  120 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 120 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 120 181 (Polychromatic418967fa.accept_16_3_8_5_1_6790 3 120 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 181 (accept_3_3 2 120 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 181 (Polychromatic418967fa.accept_19_1_6_10_1_3366 1 120 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 119 181 (Eq.refl Bool.true)
  (allA_of_3_1 63 119 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 118 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 118 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 118 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 181 (accept_3_3 62 118 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 118 181 (Polychromatic418967fa.accept_14_5_6_13_1_3145 61 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 181
  (Polychromatic418967fa.accept_13_8_1_12_1_762 60 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 181 (accept_3_3 59 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 181 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 118 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 181 (accept_3_3 56 118 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 181
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 181 (accept_3_3 53 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 118 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 181 (accept_3_3 50 118 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 181
  (Polychromatic418967fa.accept_15_3_13_1_1_479 48 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 181 (accept_3_3 47 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 181 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 118 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 181 (accept_3_3 44 118 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 181
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 118 181 (accept_3_3 41 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 118 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 118 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 118 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 118 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 181 (accept_3_3 38 118 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 181
  (Polychromatic418967fa.accept_13_11_1_12_1_742 37 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 118 181 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 118 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 118 181 (accept_3_3 35 118 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 118 181 (Polychromatic418967fa.accept_13_8_1_12_1_762 34 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 118 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 118 181 (accept_3_3 32 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 118 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 118 181 (Polychromatic418967fa.accept_24_6_22_13_1_8579 30 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 181 (accept_3_3 29 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 118
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 118 181 (accept_3_3 26 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 118 181 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 118 181 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 181 (accept_3_3 23 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 181 (Polychromatic418967fa.accept_17_5_16_11_1_3998 22 118
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 181 (accept_3_3 20 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 181 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 181 (accept_3_3 17 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 118
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 181 (accept_3_3 14 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 181 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 181 (accept_3_3 11 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 118
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 181 (accept_3_3 8 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 181 (Polychromatic418967fa.accept_19_6_4_10_1_3342 6 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 181 (accept_3_3 5 118 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 118 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 181 (accept_3_3 2 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 181 (Polychromatic418967fa.accept_16_1_6_5_1_4385 1 118 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 117 181
  (Eq.refl Bool.true) (allA_succ_of_accept 64 117 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 117 181 (accept_3_3 62 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 117 181 (Polychromatic418967fa.accept_25_11_17_6_1_10423 61 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 181 (accept_3_3 59 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 117 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 117 181 (accept_3_3 56 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 117 181 (Polychromatic418967fa.accept_17_4_15_11_1_6465 55 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 117 181 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 181 (accept_3_3 53 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 117 181 (accept_3_3 50 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 117 181 (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 181 (Polychromatic418967fa.accept_14_6_5_13_1_367 48 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 181 (accept_3_3 47 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 117 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 181
  (Polychromatic418967fa.accept_19_7_3_10_1_4674 45 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 117 181 (accept_3_3 44 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 117 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 117 181 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 181 (accept_3_3 41 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 117 181 (accept_3_3 38 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 117 181 (Polychromatic418967fa.accept_25_12_17_6_1_10422 37 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 181 (accept_3_3 35 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 117 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 181
  (Polychromatic418967fa.accept_17_16_15_11_1_10421 33 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 181 (accept_3_3 32 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 181 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 117 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 181 (Polychromatic418967fa.accept_17_13_15_11_1_2936 30
  117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 181 (accept_3_3 29
  117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 181
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 117 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 117 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 181 (accept_3_3 26 117 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 117 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 117 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 181 (Polychromatic418967fa.accept_10_4_7_1_1_471
  24 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 181 (accept_3_3 23
  117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 181
  (Polychromatic418967fa.accept_6_4_3_1_1_57 22 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 117 181 (Polychromatic418967fa.accept_17_4_15_11_1_6465 21 117 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 181 (accept_3_3 20 117 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 181 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 117 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 181 (accept_3_3 17 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 117 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 181 (accept_3_3 14 117 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 181 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 117 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 181
  (Polychromatic418967fa.accept_19_12_3_10_1_10420 12 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 181 (accept_3_3 11 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 117 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 181 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 117 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 181 (accept_3_3 8 117 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 181 (Polychromatic418967fa.accept_19_7_3_10_1_4674
  7 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 181
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 181 (accept_3_3 5 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 117 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 181 (accept_3_3 2 117 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 117 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 116 181 (Eq.refl Bool.true)
  (allA_of_3_1 66 116 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 115 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 115 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 181 (accept_3_3 65 115 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 115 181 (Polychromatic418967fa.accept_10_4_5_1_1_497 64 115 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 181
  (Polychromatic418967fa.accept_17_12_13_11_1_2910 63 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 115 181 (accept_3_3 62 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 115 181 (Polychromatic418967fa.accept_19_4_1_10_1_7447 61 115 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 115 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 181 (accept_3_3 59 115 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 181 (accept_3_3 56 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 181 (Polychromatic418967fa.accept_19_17_1_10_1_4671 55 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 181 (accept_3_3 53 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 181 (Polychromatic418967fa.accept_14_10_3_13_1_1530 52 115 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 181 (accept_3_3 50 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 181 (accept_3_3 47 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 115 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 181
  (Polychromatic418967fa.accept_19_7_1_10_1_4702 45 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 181 (accept_3_3 44 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 181 (Polychromatic418967fa.accept_13_4_11_12_1_1318 43 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 181 (accept_3_3 41 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 115 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 181 (accept_3_3 38 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 181 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 115 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 181 (accept_3_3 35 115 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 181 (accept_3_3 32 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 181 (accept_3_3 29 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 181 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 115 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 181
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 115 181 (accept_3_3 26 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 115 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 115 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 115 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 181 (accept_3_3 23 115 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 181 (accept_3_3 20 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 181 (accept_3_3 17 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 115 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 181 (accept_3_3 14 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 181 (accept_3_3 11 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 181 (accept_3_3 8 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 181 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 181 (accept_3_3 5 115 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 115 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 181 (accept_3_3 2 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 181 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 115 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 114
  181 (Eq.refl Bool.true) (allA_succ_of_accept 67 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 114 181 (accept_3_3 65 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 114 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 181 (accept_3_3 62 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 114 181 (accept_3_3 59 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 114 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 114 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 181 (accept_3_3 56 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 181
  (Polychromatic418967fa.accept_11_10_4_5_1_359 54 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 114 181 (accept_3_3 53 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 114 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 181 (accept_3_3 50 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 114 181 (accept_3_3 47 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 114 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 114 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 181 (accept_3_3 44 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 181
  (Polychromatic418967fa.accept_23_19_22_20_1_10419 42 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 114 181 (accept_3_3 41 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 114 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 114 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 181 (accept_3_3 38 114 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 181 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  37 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 181 (accept_3_3 35 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 114 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 181 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 181 (accept_3_3 32 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 181 (accept_3_3 29 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 181 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 181 (accept_3_3 26 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 181 (accept_3_3 23 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 114 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 181 (accept_3_3 20 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 181 (accept_3_3 17 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 181 (accept_3_3 14 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 181 (accept_3_3 11 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 181 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 181 (accept_3_3 8 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 181
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 181 (accept_3_3 5 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 114 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 181 (accept_3_3 2 114 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 114 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 113 181 (Eq.refl Bool.true)
  (allA_of_3_1 69 113 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 112 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 112 181 (accept_3_3 68 112 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 112 181 (Polychromatic418967fa.accept_21_4_7_13_1_8757 67 112 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 112 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 112 181 (accept_3_3 65 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 112 181 (Polychromatic418967fa.accept_19_7_17_10_1_4630 64 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 112 181 (accept_3_3 62 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 112 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 112 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 112 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 112 181 (accept_3_3 59 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 112 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 112 181 (accept_3_3 56 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 112 181 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 112 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 112 181
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 112 181 (accept_3_3 53 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 112 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 112 181 (accept_3_3 50 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 112 181 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 112 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 112 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 112 181 (accept_3_3 47 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 112 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 112 181 (accept_3_3 44 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 112 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 112 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 112 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 112 181 (accept_3_3 41 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 112 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045 40 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 181 (accept_3_3 38 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 181 (Polychromatic418967fa.accept_17_3_10_11_1_7848 37 112 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 181
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 112 181 (accept_3_3 35 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 112 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 181 (accept_3_3 32 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 112 181 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 112 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 112 181 (accept_3_3 29 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 112 181 (Polychromatic418967fa.accept_27_1_4_19_1_10418 28 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 181 (accept_3_3 26 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 112 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 112 181 (accept_3_3 23 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 112 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 181 (accept_3_3 20 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 181 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 112 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 181
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 181 (accept_3_3 17 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 181 (accept_3_3 14 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 181 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 112 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 181 (accept_3_3 11 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 181 (accept_3_3 8 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 112 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 181 (accept_3_3 5 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 181 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 112 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 181 (accept_3_3 2 112 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 112 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 111 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 111 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 111 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 111 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 111 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 181 (accept_3_3 68 111 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 181 (Polychromatic418967fa.accept_9_4_3_1_1_154
  67 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 181 (accept_3_3 65 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 181 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 181 (accept_3_3 62 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 111 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 181 (accept_3_3 59 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 181 (Polychromatic418967fa.accept_12_9_3_1_1_303 57 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 181 (accept_3_3 56 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 181 (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 111
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 181 (accept_3_3 53 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 111 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 181 (accept_3_3 50 111 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 181
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 181 (accept_3_3 47 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 181 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 181 (accept_3_3 44 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 111 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 181 (accept_3_3 41 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 181 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 181 (accept_3_3 38 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 181 (Polychromatic418967fa.accept_13_11_7_12_1_2758 37 111
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 181
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 181 (accept_3_3 35 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 111 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 181 (accept_3_3 32 111 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 181 (Polychromatic418967fa.accept_9_4_3_1_1_154
  31 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 181 (accept_3_3 29 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 181 (Polychromatic418967fa.accept_18_9_3_1_1_2559 27 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 181 (accept_3_3 26 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 111 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 181 (accept_3_3 23 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 181 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 181 (accept_3_3 20 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 181 (Polychromatic418967fa.accept_13_6_7_12_1_3504 19 111
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 181 (accept_3_3 17 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 111 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 181 (accept_3_3 14 111 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 181
  (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 181 (accept_3_3 11 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 181 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 111 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 181 (accept_3_3 8 111 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 181 (accept_3_3 5 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 181 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 111 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 181 (accept_3_3 2 111 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 181 (Polychromatic418967fa.accept_16_1_15_5_1_708 1 111 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 110 181 (Eq.refl Bool.true)
  (allA_of_3_1 72 110 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 109 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 109 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 109 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 181 (accept_3_3 71 109 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 109 181 (Polychromatic418967fa.accept_11_4_10_5_1_1202 70 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 181
  (Polychromatic418967fa.accept_13_4_5_12_1_751 69 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 181 (accept_3_3 68 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 181 (Polychromatic418967fa.accept_13_2_5_12_1_2043 67 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 181 (accept_3_3 65 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 181 (Polychromatic418967fa.accept_17_13_7_11_1_3985 64 109 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 181
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 181 (accept_3_3 62 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 181 (Polychromatic418967fa.accept_13_8_5_12_1_2755 60 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 181 (accept_3_3 59 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 109 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 181
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 57 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 181 (accept_3_3 56 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 181 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 181 (accept_3_3 53 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 181 (accept_3_3 50 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 181 (Polychromatic418967fa.accept_16_1_13_5_1_2280 49 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 181 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 181 (accept_3_3 47 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 181 (Polychromatic418967fa.accept_13_7_5_12_1_1305 46 109
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 181 (accept_3_3 44 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 181 (Polychromatic418967fa.accept_13_4_5_12_1_751 43 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 181 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 181 (accept_3_3 41 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 109 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 181
  (Polychromatic418967fa.accept_11_6_10_5_1_341 39 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 181 (accept_3_3 38 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 181 (Polychromatic418967fa.accept_27_9_1_19_1_4355 36 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 181 (accept_3_3 35 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 181 (Polychromatic418967fa.accept_13_8_5_12_1_2755 34 109
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 181 (accept_3_3 32 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 181 (accept_3_3 29 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 181 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 181
  (Polychromatic418967fa.accept_13_1_5_12_1_306 27 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 181 (accept_3_3 26 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 181 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 181 (accept_3_3 23 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 181 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 181
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 181 (accept_3_3 20 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 181 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 181 (accept_3_3 17 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 109 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 181
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 181 (accept_3_3 14 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 181 (Polychromatic418967fa.accept_17_13_7_11_1_3985 13 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 181 (accept_3_3 11 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 181 (accept_3_3 8 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 181 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 181 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 181 (accept_3_3 5 109 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 181 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 109 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 181 (accept_3_3 2 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 181 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 109 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  108 181 (Eq.refl Bool.true) (allA_succ_of_accept 73 108 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 108 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 108 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 108 181 (accept_3_3 71 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 108 181 (Polychromatic418967fa.accept_13_5_4_12_1_2058 70 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 108 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 181 (accept_3_3 68 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 108 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 108 181
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 66 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 108 181 (accept_3_3 65 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 108 181 (Polychromatic418967fa.accept_15_4_3_1_1_487 64 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 108 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 181 (accept_3_3 62 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 181 (Polychromatic418967fa.accept_19_4_13_10_1_7382 61 108
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 108 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 108 181 (accept_3_3 59 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 108 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 108 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 181 (accept_3_3 56 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 181 (Polychromatic418967fa.accept_13_3_4_12_1_36 55 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 181
  (Polychromatic418967fa.accept_13_2_4_12_1_745 54 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 108 181 (accept_3_3 53 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 108 181 (Polychromatic418967fa.accept_16_4_12_5_1_2287 52 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 108 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 181 (accept_3_3 50 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 181
  (Polychromatic418967fa.accept_21_6_3_13_1_2742 48 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 181 (accept_3_3 47 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 108 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 108 181 (Polychromatic418967fa.accept_14_3_10_13_1_339 45 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 181 (accept_3_3 44 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 108
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 181
  (Polychromatic418967fa.accept_13_3_4_12_1_36 42 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 108 181 (accept_3_3 41 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 108 181 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 108 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 181 (accept_3_3 38 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 181
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 181 (accept_3_3 35 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 108 181 (Polychromatic418967fa.accept_13_8_4_12_1_2753 34 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 181 (accept_3_3 32 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 181 (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 108 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 108 181 (accept_3_3 29 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 108 181 (Polychromatic418967fa.accept_13_2_4_12_1_745 28 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 108 181 (Polychromatic418967fa.accept_20_7_8_1_1_5856 27 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 181 (accept_3_3 26 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 108 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 181
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 108 181 (accept_3_3 23 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 181 (Polychromatic418967fa.accept_17_5_6_11_1_3974 22 108 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 181 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 108
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 181 (accept_3_3 20 108
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 181
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 108 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 108 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 181 (accept_3_3 17 108 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 108 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 181 (Polychromatic418967fa.accept_13_2_4_12_1_745
  15 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 181 (accept_3_3 14
  108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 181
  (Polychromatic418967fa.accept_10_3_8_1_1_182 13 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 108 181 (Polychromatic418967fa.accept_17_12_6_11_1_7880 12 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 181 (accept_3_3 11 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 181 (Polychromatic418967fa.accept_16_10_12_5_1_2254 10 108 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 108 181 (accept_3_3 8 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  108 181 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 108 181 (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 181 (accept_3_3 5 108 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 108 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 181
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 108 181 (accept_3_3 2 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  108 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 108 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75
  107 181 (Eq.refl Bool.true) (allA_of_3_1 75 107 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 106 181
  (Eq.refl Bool.true) (allA_succ_of_accept 75 106 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 181 (accept_3_3 74 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 181 (Polychromatic418967fa.accept_21_10_1_13_1_7167 73 106
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 181 (accept_3_3 71 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 181 (Polychromatic418967fa.accept_13_5_2_12_1_1301 70 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 181 (accept_3_3 68 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 181 (accept_3_3 65 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 181 (Polychromatic418967fa.accept_11_9_7_5_1_749 64 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 181 (accept_3_3 62 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 181 (accept_3_3 59 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 181 (accept_3_3 56 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 181 (accept_3_3 53 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 181 (accept_3_3 50 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 181 (accept_3_3 47 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 181 (Polychromatic418967fa.accept_16_14_10_5_1_1393 46 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 181 (accept_3_3 44 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 181 (accept_3_3 41 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 181 (accept_3_3 38 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 181
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 106 181 (accept_3_3 35 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 106 181 (Polychromatic418967fa.accept_19_15_11_10_1_2206 34 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 181 (accept_3_3 32
  106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 106 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 106 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 106 181 (accept_3_3 29 106 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 106 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 106 181 (accept_3_3 26 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 106 181 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 106 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 106 181 (accept_3_3 23 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 106 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 106 181 (accept_3_3 20 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 106 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 106 181 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 106 181 (accept_3_3 17 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 106 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 106 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 106 181 (accept_3_3 14 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 106 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 106 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 181 (accept_3_3 11 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 181 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 106 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 181 (accept_3_3 8 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 181 (accept_3_3 5 106 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 106 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 181 (accept_3_3 2 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 181 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 106 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 105 181 (Eq.refl Bool.true) (allA_succ_of_accept 76 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 105 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 75 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 105 181 (accept_3_3 74 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 105 181 (Polychromatic418967fa.accept_13_8_1_12_1_762 73 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 105 181 (Polychromatic418967fa.accept_25_22_5_6_1_10417 72 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 181 (accept_3_3 71 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 105 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 105 181
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 105 181 (accept_3_3 68 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 105 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 105 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 181 (accept_3_3 65 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 105 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 105 181 (accept_3_3 62 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 105 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 105 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 181 (accept_3_3 59 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 105 181 (accept_3_3 56 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 105 181 (Polychromatic418967fa.accept_20_15_5_1_1_5899 55 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 105 181 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 181 (accept_3_3 53 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 105 181 (accept_3_3 50 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 105 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 105 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 181 (accept_3_3 47 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 181
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 105 181 (accept_3_3 44 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 105 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 105 181 (Polychromatic418967fa.accept_27_15_24_19_1_10416 42 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 181 (accept_3_3 41 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 181 (accept_3_3 38 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 105 181 (Polychromatic418967fa.accept_13_11_1_12_1_742 37 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 181 (accept_3_3 35 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 181
  (Polychromatic418967fa.accept_16_1_9_5_1_5443 33 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 105 181 (accept_3_3 32 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 105 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 105 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 181 (accept_3_3 29 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 181 (accept_3_3 26 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 105 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 105 181 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 181 (accept_3_3 23 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 105 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 105 181 (accept_3_3 20 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 105 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 105 181 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 181 (accept_3_3 17 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 105 181 (accept_3_3 14 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 181 (accept_3_3 11 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 181
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 181 (accept_3_3 8 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 181 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 181 (accept_3_3 5 105 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 181 (accept_3_3 2 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 105 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 104 181 (Eq.refl Bool.true) (allA_of_3_1 78 104 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 103 181
  (Eq.refl Bool.true) (allA_succ_of_accept 78 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 181 (accept_3_3 77 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 181 (Polychromatic418967fa.accept_11_10_4_5_1_359 76 103
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 75 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 181 (accept_3_3 74 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 181 (Polychromatic418967fa.accept_19_16_8_10_1_7431 73 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 181 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 181 (accept_3_3 71 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 103 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 69 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 181 (accept_3_3 68 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 181 (accept_3_3 65 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 181
  (Polychromatic418967fa.accept_15_3_13_1_1_479 63 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 181 (accept_3_3 62 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 181 (accept_3_3 59 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 181 (accept_3_3 56 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 181 (accept_3_3 53 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 181 (accept_3_3 50 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 181 (Polychromatic418967fa.accept_19_11_8_10_1_8901 49 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 181 (accept_3_3 47 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 181
  (Polychromatic418967fa.accept_20_5_3_1_1_10415 45 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 181 (accept_3_3 44 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 181 (accept_3_3 41 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 103 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 181 (accept_3_3 38 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 181 (Polychromatic418967fa.accept_19_18_8_10_1_7489 37 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 181 (accept_3_3 35 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 181 (accept_3_3 32 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 181 (Polychromatic418967fa.accept_19_12_8_10_1_8948 31 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 181 (accept_3_3 29 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 181 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 181
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 103 181 (accept_3_3 26 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 103 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 103 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 103 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 181 (accept_3_3 23 103 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 181 (accept_3_3 20 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 181 (Polychromatic418967fa.accept_24_19_7_13_1_10414 19 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 181 (accept_3_3 17 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 103 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 181 (accept_3_3 14 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 181 (Polychromatic418967fa.accept_20_13_3_1_1_3065 13 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 181 (accept_3_3 11 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 181
  (Polychromatic418967fa.accept_22_9_15_5_1_10413 9 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 181 (accept_3_3 8 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 181 (accept_3_3 5 103 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 103 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 181 (accept_3_3 2 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 103 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 102 181 (Eq.refl Bool.true) (allA_succ_of_accept 79 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50
  79 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 102 181 (accept_3_3 77 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 102 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 181 (accept_3_3 74 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 102 181 (accept_3_3 71 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 102 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 102 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 181 (accept_3_3 68 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 181 (accept_3_3 65 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 102 181 (Polychromatic418967fa.accept_15_4_12_1_1_1081 64 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 181 (accept_3_3 62 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 181 (accept_3_3 59 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 181 (Polychromatic418967fa.accept_18_3_12_1_1_3787 57 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 181 (accept_3_3 56 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 102 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 181 (accept_3_3 53 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 102 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 181 (accept_3_3 50 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 181
  (Polychromatic418967fa.accept_21_6_18_13_1_8767 48 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 181 (accept_3_3 47 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 102 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 102 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 181 (accept_3_3 44 102 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 181 (accept_3_3 41 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 181 (accept_3_3 38 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 181
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 181 (accept_3_3 35 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 181 (accept_3_3 32 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 181 (accept_3_3 29 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 181 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 181 (accept_3_3 26 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 181 (accept_3_3 23 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 181 (Polychromatic418967fa.accept_18_3_12_1_1_3787 21 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 181 (accept_3_3 20 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 181
  (Polychromatic418967fa.accept_19_18_7_10_1_9001 18 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 181 (accept_3_3 17 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 102 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 181 (accept_3_3 14 102 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 181 (Polychromatic418967fa.accept_9_4_3_1_1_154
  13 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 181 (accept_3_3 11 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 181 (accept_3_3 8 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 181 (accept_3_3 5 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 102 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 181 (accept_3_3 2 102 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 181 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 102 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 101 181 (Eq.refl
  Bool.true) (allA_of_3_1 81 101 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 100 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 100 181 (accept_3_3 80 100 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 100 181 (Polychromatic418967fa.accept_16_15_4_5_1_1411 79 100 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 100 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 100 181 (accept_3_3 77 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 100 181 (Polychromatic418967fa.accept_16_12_4_5_1_2273 76 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 100 181 (accept_3_3 74 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 100 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 100 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 100 181
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 100 181 (accept_3_3 71 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 100 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 100 181 (accept_3_3 68 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 100 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 100 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 100 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 100 181 (accept_3_3 65 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 100 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 181 (accept_3_3 62 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 100 181 (Polychromatic418967fa.accept_11_6_1_5_1_2388 61 100 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 100 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 100 181 (accept_3_3 59 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 100 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 100 181 (accept_3_3 56 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 100 181 (Polychromatic418967fa.accept_13_3_9_12_1_2062 55 100 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 100 181
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 54 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 100 181 (accept_3_3 53 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 100 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 100 181 (accept_3_3 50 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 100 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 100 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 100 181
  (Polychromatic418967fa.accept_21_6_16_13_1_4100 48 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 100 181 (accept_3_3 47 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 100 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 100 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 100 181 (accept_3_3 44 100 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 43
  100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 181
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 181 (accept_3_3 41 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 100 181 (Polychromatic418967fa.accept_16_8_4_5_1_4379 40 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 181 (accept_3_3 38 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 100 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 100 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 100 181 (accept_3_3 35 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 100 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 181 (accept_3_3 32 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 100 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 100 181
  (Polychromatic418967fa.accept_17_13_15_11_1_2936 30 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 100 181 (accept_3_3 29 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 100 181 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 100 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 181 (accept_3_3 26 100 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 100 181 (Polychromatic418967fa.accept_7_4_2_6_1_337
  25 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 100 181 (accept_3_3 23 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 100 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 181 (accept_3_3 20 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 100 181 (Polychromatic418967fa.accept_21_19_16_13_1_4099 19 100 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 100 181 (accept_3_3 17 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 100 181 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 181 (accept_3_3 14 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 181 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 100 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 181
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 181 (accept_3_3 11 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 100 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 181 (accept_3_3 8 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 100 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 181
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 100 181 (accept_3_3 5 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  100 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 100 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 181 (accept_3_3 2 100 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 100 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 99 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 181 (Polychromatic418967fa.accept_12_9_3_1_1_303
  81 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 181 (accept_3_3 80
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 181 (accept_3_3 77 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 99 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 75
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 181 (accept_3_3 74 99
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 181
  (Polychromatic418967fa.accept_19_16_4_10_1_7474 73 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 99 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 181 (accept_3_3 71 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 181 (Polychromatic418967fa.accept_12_9_3_1_1_303
  69 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 181 (accept_3_3 68
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 181
  (Polychromatic418967fa.accept_15_7_9_1_1_473 67 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 181 (accept_3_3 65 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 99 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 181 (Polychromatic418967fa.accept_14_7_1_13_1_357
  63 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 181 (accept_3_3 62
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 99 181 (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 181 (accept_3_3 59 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 181 (Polychromatic418967fa.accept_12_9_3_1_1_303
  57 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 181 (accept_3_3 56
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 181
  (Polychromatic418967fa.accept_10_5_9_1_1_187 55 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 181 (accept_3_3 53 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 99 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 51
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 181 (accept_3_3 50 99
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 181
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 99 181 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 181 (accept_3_3 47 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 181 (Polychromatic418967fa.accept_10_5_9_1_1_187
  45 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 181 (accept_3_3 44
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 181
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 43 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 181 (accept_3_3 41 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 99 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 181 (Polychromatic418967fa.accept_18_3_9_1_1_3690
  39 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 181 (accept_3_3 38
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 99 181 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 181 (accept_3_3 35 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 33
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 181 (accept_3_3 32 99
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 181
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 181 (accept_3_3 29 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 99 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  27 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 181 (accept_3_3 26
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 181
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 99 181 (Polychromatic418967fa.accept_16_8_3_5_1_5512 24 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 181 (accept_3_3 23 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 181 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 181 (accept_3_3 20
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 181 (accept_3_3 17 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 99 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 181 (Polychromatic418967fa.accept_10_5_9_1_1_187
  15 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 181 (accept_3_3 14
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 181
  (Polychromatic418967fa.accept_19_13_4_10_1_7452 13 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 99 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 181 (accept_3_3 11 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 99 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9
  99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 181 (accept_3_3 8 99 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 181 (Polychromatic418967fa.accept_13_7_8_12_1_2810
  7 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 181 (accept_3_3 5 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 99 181 (Polychromatic418967fa.accept_17_3_14_11_1_5243 3 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 181 (accept_3_3 2 99 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 99 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 99 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 98 181 (Eq.refl
  Bool.true) (allA_of_3_1 84 98 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 97 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 84 97 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 97 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 181 (accept_3_3 83 97 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 97 181 (Polychromatic418967fa.accept_17_14_12_11_1_4063 82 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 181
  (Polychromatic418967fa.accept_15_6_7_1_1_93 81 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 181 (accept_3_3 80 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 181 (Polychromatic418967fa.accept_16_15_1_5_1_2265 79 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 78 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 181 (accept_3_3 77 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 76 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 75 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 181 (accept_3_3 74 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 181 (Polychromatic418967fa.accept_11_7_9_5_1_338 73 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 181 (Polychromatic418967fa.accept_13_7_6_12_1_2027 72 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 181 (accept_3_3 71 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 181 (Polychromatic418967fa.accept_13_5_6_12_1_2750 70 97
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 69 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 181 (accept_3_3 68 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 181 (accept_3_3 65 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 181 (Polychromatic418967fa.accept_10_4_7_1_1_471 64 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 181
  (Polychromatic418967fa.accept_16_15_1_5_1_2265 63 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 181 (accept_3_3 62 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 181 (Polychromatic418967fa.accept_16_13_1_5_1_5469 61 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 181 (accept_3_3 59 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 181 (accept_3_3 56 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 181 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 181 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 181 (accept_3_3 53 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 181 (accept_3_3 50 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 181 (accept_3_3 47 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 181 (Polychromatic418967fa.accept_10_6_7_1_1_1297 46 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 181
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 181 (accept_3_3 44 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 181 (Polychromatic418967fa.accept_19_5_2_10_1_3371 43 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 181 (accept_3_3 41 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 181 (accept_3_3 38 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 181 (Polychromatic418967fa.accept_19_18_2_10_1_10412 37 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 181 (accept_3_3 35 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 181 (Polychromatic418967fa.accept_10_4_7_1_1_471 34 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 181 (accept_3_3 32 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 181 (accept_3_3 29 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 181
  (Polychromatic418967fa.accept_19_8_2_10_1_7415 27 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 181 (accept_3_3 26 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 181 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 181 (accept_3_3 23 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 181 (accept_3_3 20 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 181 (Polychromatic418967fa.accept_24_19_1_13_1_10411 19 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 181 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 181 (accept_3_3 17 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 181 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 181 (accept_3_3 14 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 181 (accept_3_3 11 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 181 (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 97 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 181
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 181 (accept_3_3 8 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  181 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 97 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 181 (accept_3_3 5 97 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 97 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 3
  97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 181 (accept_3_3 2 97 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 181 (Polychromatic418967fa.accept_22_1_9_5_1_10410
  1 97 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 96 181
  (Eq.refl Bool.true) (allA_succ_of_accept 85 96 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 181 (accept_3_3 83 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 82 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 181 (accept_3_3 80 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 181 (accept_3_3 77 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  96 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 181 (accept_3_3 74 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 181 (Polychromatic418967fa.accept_13_8_5_12_1_2755 73 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 181
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 181 (accept_3_3 71 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 181 (Polychromatic418967fa.accept_11_3_8_5_1_336 69 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 181 (accept_3_3 68 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 181 (accept_3_3 65 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 181 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 181 (accept_3_3 62 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 181 (accept_3_3 59 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 181 (accept_3_3 56 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 181 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 181
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 54 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 181 (accept_3_3 53 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 181 (Polychromatic418967fa.accept_19_13_1_10_1_8963 51 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 181 (accept_3_3 50 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 96 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 181 (accept_3_3 47 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 181 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 181 (accept_3_3 44 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 181
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 181 (accept_3_3 41 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 181 (accept_3_3 38 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 181 (accept_3_3 35 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 181 (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 181 (accept_3_3 32 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 96 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 181 (accept_3_3 29 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 181 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 181 (accept_3_3 26 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 181
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 181 (accept_3_3 23 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 181 (accept_3_3 20 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 181 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 181 (accept_3_3 17 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 181 (accept_3_3 14 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 181 (accept_3_3 11 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 181 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 181 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 181 (accept_3_3 8 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 181
  (Polychromatic418967fa.accept_13_6_5_12_1_307 6 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 181 (accept_3_3 5 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 96 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 181 (accept_3_3 2 96 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 95 181
  (Eq.refl Bool.true) (allA_of_3_1 87 95 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 94 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 181 (accept_3_3 86 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 94 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 85 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 94 181 (accept_3_3 83 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  94 181 (Polychromatic418967fa.accept_13_4_3_12_1_2066 82 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 94 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 94 181 (accept_3_3 80 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 94 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 94 181 (accept_3_3 77 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  94 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 76 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 181 (accept_3_3 74 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 94 181 (Polychromatic418967fa.accept_14_3_10_13_1_339 73 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 94 181 (accept_3_3 71 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  94 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 94 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 181 (accept_3_3 68 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 94 181 (accept_3_3 65 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  94 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 181 (accept_3_3 62 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 94 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 94 181 (accept_3_3 59 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  94 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 94 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 181 (accept_3_3 56 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 181
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 94 181 (accept_3_3 53 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  94 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 181 (accept_3_3 50 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 181 (Polychromatic418967fa.accept_19_11_18_10_1_1148 49 94 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 181 (accept_3_3 47 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 181 (accept_3_3 44 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 181 (accept_3_3 41 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 181 (accept_3_3 38 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 181
  (Polychromatic418967fa.accept_17_2_9_11_1_4057 36 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 181 (accept_3_3 35 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 181 (accept_3_3 32 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 181 (accept_3_3 29 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 181 (accept_3_3 26 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 181 (accept_3_3 23 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 181 (Polychromatic418967fa.accept_13_9_3_12_1_2025 22 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 181 (accept_3_3 20 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 181 (accept_3_3 17 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 181 (accept_3_3 14 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 181 (Polychromatic418967fa.accept_20_13_14_1_1_5869 13 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 181 (accept_3_3 11 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 181 (accept_3_3 8 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 181 (accept_3_3 5 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 94 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 94 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 181 (accept_3_3 2 94 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 94 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 93 181
  (Eq.refl Bool.true) (allA_succ_of_accept 88 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 181 (accept_3_3 86 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 85 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 181 (Polychromatic418967fa.accept_13_6_2_12_1_2802 84 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 181 (accept_3_3 83 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 93 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 181 (accept_3_3 80 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 181 (accept_3_3 77 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 181 (accept_3_3 74 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 181 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 181 (accept_3_3 71 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 69 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 181 (accept_3_3 68 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 181 (accept_3_3 65 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 181 (accept_3_3 62 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 181 (accept_3_3 59 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 181 (accept_3_3 56 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 181 (Polychromatic418967fa.accept_13_3_2_12_1_2797 55 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 181 (Polychromatic418967fa.accept_20_14_13_1_1_8844 54 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 181 (accept_3_3 53 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 181 (accept_3_3 50 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 181 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 181 (accept_3_3 47 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 181 (accept_3_3 44 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 181 (accept_3_3 41 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 181 (accept_3_3 38 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 181 (Polychromatic418967fa.accept_19_18_17_10_1_7444 37 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 181 (accept_3_3 35 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 181 (accept_3_3 32 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 181 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 181 (accept_3_3 29 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 181 (accept_3_3 26 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 181 (accept_3_3 23 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 181
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 181 (accept_3_3 20 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 181 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 181 (accept_3_3 17 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 181 (accept_3_3 14 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 181 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 181 (accept_3_3 11 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 181
  (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 181 (accept_3_3 8 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 93 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 93 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 181 (accept_3_3 5 93 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 181 (accept_3_3 2 93 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 93
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 92 181
  (Eq.refl Bool.true) (allA_of_3_1 90 92 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 181
  (allA_succ_of_accept 90 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 181 (accept_3_3 89 91 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 181 (Polychromatic418967fa.accept_16_8_11_5_1_3319 88 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 181
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 87 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 91 181 (accept_3_3 86 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  91 181 (Polychromatic418967fa.accept_11_8_3_5_1_355 85 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 91 181 (Polychromatic418967fa.accept_20_4_11_1_1_10409 84 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 181 (accept_3_3 83 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 181
  (Polychromatic418967fa.accept_17_13_6_11_1_4014 81 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 91 181 (accept_3_3 80 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  91 181 (Polychromatic418967fa.accept_19_3_15_10_1_4688 79 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 181 (accept_3_3 77 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 181 (Polychromatic418967fa.accept_14_6_7_13_1_3158 76 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 181
  (Polychromatic418967fa.accept_22_9_3_5_1_3856 75 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 181 (accept_3_3 74 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 181 (Polychromatic418967fa.accept_16_9_11_5_1_2279 73 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 181 (Polychromatic418967fa.accept_16_8_11_5_1_3319 72 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 181 (accept_3_3 71 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 181
  (Polychromatic418967fa.accept_21_6_7_13_1_7199 69 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 181 (accept_3_3 68 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 181 (Polychromatic418967fa.accept_20_7_11_1_1_5840 67 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 181 (accept_3_3 65 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 181 (Polychromatic418967fa.accept_14_8_7_13_1_4113 64 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 181
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 181 (accept_3_3 62 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 181 (Polychromatic418967fa.accept_19_4_15_10_1_4602 61 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 181 (Polychromatic418967fa.accept_19_3_15_10_1_4688 60 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 181 (accept_3_3 59 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 181
  (Polychromatic418967fa.accept_14_1_7_13_1_333 57 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 181 (accept_3_3 56 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 181 (Polychromatic418967fa.accept_16_7_11_5_1_4402 55 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 181 (accept_3_3 53 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 181 (Polychromatic418967fa.accept_11_8_3_5_1_355 52 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 181
  (Polychromatic418967fa.accept_21_9_7_13_1_8742 51 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 181 (accept_3_3 50 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 181 (Polychromatic418967fa.accept_19_11_15_10_1_7406 49 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 181 (Polychromatic418967fa.accept_14_6_7_13_1_3158 48 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 181 (accept_3_3 47 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 181
  (Polychromatic418967fa.accept_22_1_3_5_1_375 45 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 181 (accept_3_3 44 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 181 (Polychromatic418967fa.accept_14_1_7_13_1_333 43 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 181 (accept_3_3 41 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 181 (Polychromatic418967fa.accept_16_8_11_5_1_3319 40 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 181
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 39 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 181 (accept_3_3 38 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 181 (Polychromatic418967fa.accept_20_17_11_1_1_8865 37 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 181 (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 181 (accept_3_3 35 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 181
  (Polychromatic418967fa.accept_19_14_15_10_1_3359 33 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 91 181 (accept_3_3 32 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 91 181 (Polychromatic418967fa.accept_21_10_7_13_1_10408 31 91 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 181 (accept_3_3 29 91 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 181
  (Polychromatic418967fa.accept_19_9_15_10_1_7443 28 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 91 181 (Polychromatic418967fa.accept_20_7_11_1_1_5840 27 91 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 181 (accept_3_3 26 91 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 91 181 (Polychromatic418967fa.accept_16_9_11_5_1_2279 25 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 181
  (Polychromatic418967fa.accept_16_8_11_5_1_3319 24 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 181 (accept_3_3 23 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 181 (Polychromatic418967fa.accept_17_4_6_11_1_1030 21 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 181 (accept_3_3 20 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 181 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 91 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 181 (accept_3_3 17 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 181 (Polychromatic418967fa.accept_20_16_11_1_1_10407 16 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 181 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 181 (accept_3_3 14 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 181 (Polychromatic418967fa.accept_17_13_6_11_1_4014 13 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 181
  (Polychromatic418967fa.accept_17_12_6_11_1_7880 12 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 181 (accept_3_3 11 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 181 (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 181 (accept_3_3 8 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 181 (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 181 (accept_3_3 5 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  181 (Polychromatic418967fa.accept_17_4_6_11_1_1030 4 91 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 181 (Polychromatic418967fa.accept_19_3_15_10_1_4688 3 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 181 (accept_3_3 2 91 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 181 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 91 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 181
  (allA_succ_of_accept 89 90 181 (accept_3_3 89 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 181 (Polychromatic418967fa.accept_19_12_14_10_1_4625 88 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 181 (accept_3_3 86 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 181 (Polychromatic418967fa.accept_11_8_2_5_1_1769 85 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 181
  (Polychromatic418967fa.accept_17_16_5_11_1_7830 84 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 181 (accept_3_3 83 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  90 181 (Polychromatic418967fa.accept_14_12_6_13_1_3173 82 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 181 (Polychromatic418967fa.accept_19_5_14_10_1_8933 81 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 181 (accept_3_3 80 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 181
  (Polychromatic418967fa.accept_16_14_10_5_1_1393 78 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 181 (accept_3_3 77 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  90 181 (Polychromatic418967fa.accept_16_12_10_5_1_5457 76 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 181 (accept_3_3 74 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 181 (Polychromatic418967fa.accept_20_13_10_1_1_5903 73 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 181
  (Polychromatic418967fa.accept_19_15_14_10_1_4667 72 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 90 181 (accept_3_3 71 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 181 (Polychromatic418967fa.accept_21_7_6_13_1_10406 70 90 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 90 181 (Polychromatic418967fa.accept_19_12_14_10_1_4625 69 90
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 181 (accept_3_3 68 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 67
  90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 181
  (Polychromatic418967fa.accept_17_15_5_11_1_6468 66 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 181 (accept_3_3 65 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 181 (Polychromatic418967fa.accept_19_7_14_10_1_6034 64 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 181 (accept_3_3 62 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 181 (Polychromatic418967fa.accept_14_5_6_13_1_3145 61 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 181
  (Polychromatic418967fa.accept_16_12_10_5_1_5457 60 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 181 (accept_3_3 59 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 181 (Polychromatic418967fa.accept_17_7_5_11_1_2922 58 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 181 (Polychromatic418967fa.accept_17_6_5_11_1_4073 57 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 181 (accept_3_3 56 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 181
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 181 (accept_3_3 53 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  90 181 (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 181 (accept_3_3 50 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 181 (Polychromatic418967fa.accept_14_7_6_13_1_4111 49 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 181
  (Polychromatic418967fa.accept_22_4_2_5_1_10405 48 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 181 (accept_3_3 47 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  90 181 (Polychromatic418967fa.accept_16_14_10_5_1_1393 46 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 181 (Polychromatic418967fa.accept_16_13_10_5_1_2278 45 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 181 (accept_3_3 44 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 181
  (Polychromatic418967fa.accept_19_4_14_10_1_7467 42 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 90 181 (accept_3_3 41 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  90 181 (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 181 (accept_3_3 38 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 181 (Polychromatic418967fa.accept_19_18_14_10_1_10403 37 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 181
  (Polychromatic418967fa.accept_21_15_6_13_1_8776 36 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 181 (accept_3_3 35 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 181 (Polychromatic418967fa.accept_19_15_14_10_1_4667 34 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 181 (Polychromatic418967fa.accept_14_5_6_13_1_3145 33 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 181 (accept_3_3 32 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 181
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 181 (accept_3_3 29 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 181 (Polychromatic418967fa.accept_16_12_10_5_1_5457 28 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 181 (accept_3_3 26 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 181 (Polychromatic418967fa.accept_19_6_14_10_1_4624 25 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 181
  (Polychromatic418967fa.accept_17_7_5_11_1_2922 24 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 181 (accept_3_3 23 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 181 (Polychromatic418967fa.accept_23_22_21_20_1_10404 22 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 181 (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 181 (accept_3_3 20 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 181
  (Polychromatic418967fa.accept_19_18_14_10_1_10403 18 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 90 181 (accept_3_3 17 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 181 (Polychromatic418967fa.accept_17_16_5_11_1_7830 16 90 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 181 (accept_3_3 14 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 181
  (Polychromatic418967fa.accept_16_13_10_5_1_2278 13 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 90 181 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 90 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 181 (accept_3_3 11 90 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 90 181 (Polychromatic418967fa.accept_22_10_2_5_1_7051 10 90 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 181
  (Polychromatic418967fa.accept_20_9_10_1_1_192 9 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 181 (accept_3_3 8 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90
  181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 90 181 (Polychromatic418967fa.accept_17_6_5_11_1_4073 6 90 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 181 (accept_3_3 5 90 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 90 181 (Polychromatic418967fa.accept_19_4_14_10_1_7467 4 90 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 181 (accept_3_3 2 90 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 181 (Polychromatic418967fa.accept_19_1_14_10_1_4619
  1 90 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 181
  (allA_of_3_1 89 89 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 181 (allA_succ_of_accept 87 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 181 (accept_3_3 86 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 181 (accept_3_3 83 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 181 (accept_3_3 80 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 78 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 181 (accept_3_3 77 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 181 (accept_3_3 74 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 181 (accept_3_3 71 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 181 (accept_3_3 68 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 181 (accept_3_3 65 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 181 (Polychromatic418967fa.accept_18_10_16_1_1_1534 64 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 181 (accept_3_3 62 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 181 (accept_3_3 59 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 181 (accept_3_3 56 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 181 (accept_3_3 53 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 181 (accept_3_3 50 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 181 (accept_3_3 47 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 181 (accept_3_3 44 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 181 (accept_3_3 41 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 181 (accept_3_3 38 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 181 (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 181 (accept_3_3 35 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 181 (accept_3_3 32 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 181 (accept_3_3 29 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 181 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 181 (accept_3_3 26 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 181 (accept_3_3 23 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 181 (accept_3_3 20 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 181 (Polychromatic418967fa.accept_15_3_13_1_1_479 18 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 181 (accept_3_3 17 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 181 (accept_3_3 14 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 181 (accept_3_3 11 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 181 (accept_3_3 8 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  181 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 181 (accept_3_3 5 88 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 88 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 181 (accept_3_3 2 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  181 (Polychromatic418967fa.accept_21_1_4_13_1_7128 1 88 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 88 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 87 181 (allA_succ_of_accept 86 87 181 (accept_3_3 86 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 87 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 87 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 87 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 84 87 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 181 (accept_3_3 83 87 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 82
  87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 181 (accept_3_3 80 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 181 (accept_3_3 77 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 75 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 181 (accept_3_3 74 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 181 (Polychromatic418967fa.accept_13_8_9_12_1_2813 73 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 181 (accept_3_3 71 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 181 (accept_3_3 68 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 181 (accept_3_3 65 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 181
  (Polychromatic418967fa.accept_23_17_18_20_1_10402 63 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 87 181 (accept_3_3 62 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 87 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 87 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 181 (accept_3_3 59 87 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 181 (accept_3_3 56 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 181 (Polychromatic418967fa.accept_13_3_9_12_1_2062 55 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 181 (accept_3_3 53 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 181 (accept_3_3 50 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 181 (accept_3_3 47 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 181 (accept_3_3 44 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 181 (accept_3_3 41 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 181 (accept_3_3 38 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 181 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 181 (accept_3_3 35 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 181 (accept_3_3 32 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 181 (accept_3_3 29 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 181
  (Polychromatic418967fa.accept_16_11_7_5_1_4364 27 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 181 (accept_3_3 26 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 181 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 181 (accept_3_3 23 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 181 (accept_3_3 20 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 181 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 181 (accept_3_3 17 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 181
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 181 (accept_3_3 14 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 181 (accept_3_3 11 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 181 (accept_3_3 8 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 181 (accept_3_3 5 87 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 181 (accept_3_3 2 87 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 181
  (Polychromatic418967fa.accept_19_1_11_10_1_10401 1 87 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 87 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86
  181 (allA_of_3_1 86 86 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 181 (allA_succ_of_accept 84 85 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 181 (accept_3_3 83 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 181 (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 181 (accept_3_3 80 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 85 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 181 (accept_3_3 77 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 181 (Polychromatic418967fa.accept_10_6_5_1_1_482 76 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 181 (accept_3_3 74 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 181 (Polychromatic418967fa.accept_13_8_7_12_1_3637 73 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 181 (accept_3_3 71 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 181 (accept_3_3 68 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 67 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 181 (accept_3_3 65 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 181 (Polychromatic418967fa.accept_10_4_5_1_1_497 64 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 181 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 181 (accept_3_3 62 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 85 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 181 (accept_3_3 59 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 181 (accept_3_3 56 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 181 (Polychromatic418967fa.accept_20_15_5_1_1_5899 55 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 181 (accept_3_3 53 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 181 (accept_3_3 50 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 181 (accept_3_3 47 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 181 (Polychromatic418967fa.accept_10_6_5_1_1_482 46 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 181 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 181 (accept_3_3 44 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 85 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 181 (accept_3_3 41 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 181 (accept_3_3 38 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 181
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 181 (accept_3_3 35 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 181 (accept_3_3 32 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 181 (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 181 (accept_3_3 29 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 181 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 181 (Polychromatic418967fa.accept_23_4_16_20_1_10400 27 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 181 (accept_3_3 26 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 85 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 181 (accept_3_3 23 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 181 (accept_3_3 20 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 181
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 181 (accept_3_3 17 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 181 (accept_3_3 14 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 181 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 181 (accept_3_3 11 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 181 (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 181 (accept_3_3 8 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 181 (accept_3_3 5 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  181 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 85 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 85 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 181 (accept_3_3 2 85 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 181 (Polychromatic418967fa.accept_19_1_9_10_1_10391 1 85 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 181
  (allA_succ_of_accept 83 84 181 (accept_3_3 83 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 181 (Polychromatic418967fa.accept_15_7_9_1_1_473 82 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 181 (accept_3_3 80 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 181 (accept_3_3 77 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 181 (accept_3_3 74 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 181
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 72 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 181 (accept_3_3 71 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 181 (accept_3_3 68 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 181
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 66 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 181 (accept_3_3 65 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 181 (Polychromatic418967fa.accept_11_9_7_5_1_749 64 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 181 (Polychromatic418967fa.accept_16_15_4_5_1_1411 63 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 181 (accept_3_3 62 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 84 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 181 (accept_3_3 59 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 181 (accept_3_3 56 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 181
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 54 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 181 (accept_3_3 53 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 181 (accept_3_3 50 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 181
  (Polychromatic418967fa.accept_17_14_16_11_1_3997 48 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 84 181 (accept_3_3 47 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 181 (Polychromatic418967fa.accept_13_7_6_12_1_2027 46 84 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 84 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 84 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 181 (accept_3_3 44 84 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 43
  84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 181 (accept_3_3 41 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 181 (Polychromatic418967fa.accept_17_5_16_11_1_3998 39 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 181 (accept_3_3 38 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 181 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 84 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 181
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 181 (accept_3_3 35 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 181 (accept_3_3 32 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 181
  (Polychromatic418967fa.accept_19_11_8_10_1_8901 30 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 181 (accept_3_3 29 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 181 (Polychromatic418967fa.accept_13_2_6_12_1_1334 28 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 181 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 181 (accept_3_3 26 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 181 (accept_3_3 23 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 181 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 181 (accept_3_3 20 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 181 (Polychromatic418967fa.accept_23_19_15_20_1_10399 19 84 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 181
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 181 (accept_3_3 17 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 181 (accept_3_3 14 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 181
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 181 (accept_3_3 11 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 181 (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 181 (accept_3_3 8 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 181 (accept_3_3 5 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  181 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 84 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 181 (Polychromatic418967fa.accept_18_3_12_1_1_3787 3 84 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 181 (accept_3_3 2 84 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 181 (allA_of_3_1
  83 83 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 181 (allA_succ_of_accept 81 82 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 181 (accept_3_3 80 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 181 (accept_3_3 77 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 76 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 181 (accept_3_3 74 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 181 (Polychromatic418967fa.accept_10_3_2_1_1_839 73 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 181 (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 181 (accept_3_3 71 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 181 (Polychromatic418967fa.accept_13_5_4_12_1_2058 70 82
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 181 (accept_3_3 68 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 181 (accept_3_3 65 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 181 (accept_3_3 62 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 181 (Polychromatic418967fa.accept_16_13_2_5_1_3336 61 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 181 (accept_3_3 59 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 181 (Polychromatic418967fa.accept_19_1_6_10_1_3366 58 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 181 (accept_3_3 56 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 181 (Polychromatic418967fa.accept_13_2_4_12_1_745 54 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 181 (accept_3_3 53 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 181 (accept_3_3 50 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 181 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 181 (Polychromatic418967fa.accept_14_6_12_13_1_3180 48 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 181 (accept_3_3 47 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 82 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 181 (accept_3_3 44 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 181 (Polychromatic418967fa.accept_13_3_4_12_1_36 42 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 181 (accept_3_3 41 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 181 (accept_3_3 38 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 181 (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 181 (accept_3_3 35 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 181 (Polychromatic418967fa.accept_13_8_4_12_1_2753 34 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 181 (accept_3_3 32 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 181 (Polychromatic418967fa.accept_23_7_13_20_1_10398 30 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 181 (accept_3_3 29 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 82 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 181 (accept_3_3 26 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 181 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 181 (accept_3_3 23 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 82 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 181 (accept_3_3 20 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 181 (accept_3_3 17 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 181 (accept_3_3 14 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 181 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 181 (Polychromatic418967fa.accept_17_12_14_11_1_998 12 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 181 (accept_3_3 11 82 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 181 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 82
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 181 (accept_3_3 8 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 82 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 181 (accept_3_3 5 82 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 82 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 181 (accept_3_3 2 82 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 82
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 181
  (allA_succ_of_accept 80 81 181 (accept_3_3 80 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 181 (Polychromatic418967fa.accept_15_3_6_1_1_1834 78 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 181 (accept_3_3 77 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 181 (accept_3_3 74 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 181 (accept_3_3 71 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 181
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 69 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 181 (accept_3_3 68 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 181 (Polychromatic418967fa.accept_13_2_3_12_1_735 67 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 181 (accept_3_3 65 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 181 (accept_3_3 62 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 181 (accept_3_3 59 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 181
  (Polychromatic418967fa.accept_16_9_1_5_1_2282 57 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 181 (accept_3_3 56 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 181 (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 181 (accept_3_3 53 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 181 (accept_3_3 50 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 181 (Polychromatic418967fa.accept_17_15_13_11_1_4031 49 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 181 (Polychromatic418967fa.accept_13_9_3_12_1_2025 48 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 181 (accept_3_3 47 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 81 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 181 (accept_3_3 44 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 181 (Polychromatic418967fa.accept_11_10_4_5_1_359 43 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 181 (Polychromatic418967fa.accept_18_6_9_1_1_3769 42 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 181 (accept_3_3 41 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 181 (accept_3_3 38 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 181 (accept_3_3 35 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 181 (accept_3_3 32 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 181 (accept_3_3 29 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 181 (accept_3_3 26 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 181 (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 181 (accept_3_3 23 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 181
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 181 (accept_3_3 20 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 181 (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 181 (accept_3_3 17 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 181 (accept_3_3 14 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 181 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 181 (accept_3_3 11 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 181 (accept_3_3 8 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  181 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 181 (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 181 (accept_3_3 5 81 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 181 (accept_3_3 2 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  181 (Polychromatic418967fa.accept_22_1_15_5_1_10397 1 81 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 181 (allA_of_3_1 80 80 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 181
  (allA_succ_of_accept 78 79 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 181 (accept_3_3 77 79 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 75
  79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 181 (accept_3_3 74 79
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 181 (Polychromatic418967fa.accept_7_3_2_6_1_56
  73 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 181
  (Polychromatic418967fa.accept_10_2_9_1_1_185 72 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 181 (accept_3_3 71 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 181 (accept_3_3 68 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 181 (accept_3_3 65 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 181 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 181 (accept_3_3 62 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 181 (Polychromatic418967fa.accept_21_19_16_13_1_4099 61 79 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 181 (accept_3_3 59 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 181 (accept_3_3 56 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 181 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 181 (accept_3_3 53 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 181 (accept_3_3 50 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 181 (accept_3_3 47 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 181 (accept_3_3 44 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 181 (accept_3_3 41 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 181 (accept_3_3 38 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 181 (Polychromatic418967fa.accept_13_11_1_12_1_742 37 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 181 (accept_3_3 35 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 181 (accept_3_3 32 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 181 (accept_3_3 29 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 181 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 181 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 181 (accept_3_3 26 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 79 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 181 (accept_3_3 23 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 181 (accept_3_3 20 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 181 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 181 (accept_3_3 17 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 181 (Polychromatic418967fa.accept_18_16_7_1_1_6332 16 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 181 (accept_3_3 14 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 181 (accept_3_3 11 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 181 (Polychromatic418967fa.accept_19_9_3_10_1_6017 9 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 181 (accept_3_3 8 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 181 (Polychromatic418967fa.accept_19_7_3_10_1_4674 7 79 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 181 (accept_3_3 5 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 181 (accept_3_3 2 79 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 181
  (allA_succ_of_accept 77 78 181 (accept_3_3 77 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 181 (accept_3_3 74 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 73 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 181 (accept_3_3 71 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 181 (accept_3_3 68 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 181 (accept_3_3 65 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 181 (Polychromatic418967fa.accept_15_4_3_1_1_487 64 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 181 (accept_3_3 62 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 181
  (Polychromatic418967fa.accept_21_18_15_13_1_4130 60 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 78 181 (accept_3_3 59 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 78 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 78 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 78 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 181 (accept_3_3 56 78 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55
  78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 181 (accept_3_3 53 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 181 (accept_3_3 50 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 181 (accept_3_3 47 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 181 (Polychromatic418967fa.accept_19_8_2_10_1_7415 46 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 181 (Polychromatic418967fa.accept_18_9_6_1_1_3687 45 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 181 (accept_3_3 44 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 181
  (Polychromatic418967fa.accept_16_10_14_5_1_5496 42 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 181 (accept_3_3 41 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 181 (accept_3_3 38 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 181
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 181 (accept_3_3 35 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 181 (accept_3_3 32 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 181 (accept_3_3 29 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 181 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 181 (accept_3_3 26 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 181
  (Polychromatic418967fa.accept_19_5_2_10_1_3371 24 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 181 (accept_3_3 23 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 181 (accept_3_3 20 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 181
  (Polychromatic418967fa.accept_17_1_10_11_1_2943 18 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 181 (accept_3_3 17 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 181 (accept_3_3 14 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 181 (accept_3_3 11 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 181 (Polychromatic418967fa.accept_16_10_14_5_1_5496 10 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 181 (accept_3_3 8 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 181
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 181 (accept_3_3 5 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  181 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 78 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 181 (accept_3_3 2 78 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 181 (Polychromatic418967fa.accept_17_1_10_11_1_2943 1 78 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 181 (allA_of_3_1 77 77
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 181 (allA_succ_of_accept 75 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 181 (accept_3_3 74 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 181 (accept_3_3 71 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 181 (accept_3_3 68 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 67 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 181 (accept_3_3 65 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 181 (Polychromatic418967fa.accept_26_12_24_25_1_10396 64 76 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 181 (accept_3_3 62 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 181 (accept_3_3 59 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 181 (accept_3_3 56 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 181 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 181 (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 181 (accept_3_3 53 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 76 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 181 (accept_3_3 50 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 181 (accept_3_3 47 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 181 (accept_3_3 44 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 181 (accept_3_3 41 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 181 (Polychromatic418967fa.accept_13_1_11_12_1_1322 40 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 181 (accept_3_3 38 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 181 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 181 (accept_3_3 35 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 76 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 181 (accept_3_3 32 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 181 (Polychromatic418967fa.accept_17_14_8_11_1_4052 31 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 181 (accept_3_3 29 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 181 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 181 (accept_3_3 26 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 181 (accept_3_3 23 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 181 (accept_3_3 20 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 181 (Polychromatic418967fa.accept_14_5_6_13_1_3145 19 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 181 (Polychromatic418967fa.accept_17_1_8_11_1_6471 18 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 181 (accept_3_3 17 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 76 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 181 (accept_3_3 14 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 181 (Polychromatic418967fa.accept_22_13_10_5_1_10395 13 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 181 (accept_3_3 11 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 76 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 181 (accept_3_3 8 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 76 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 181 (accept_3_3 5 76 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 181 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 76 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 181 (accept_3_3 2 76 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 76
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 181 (allA_succ_of_accept
  74 75 181 (accept_3_3 74 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 181
  (Polychromatic418967fa.accept_11_7_9_5_1_338 73 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 181 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 75 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 181 (accept_3_3 71 75 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 69
  75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 181 (accept_3_3 68 75
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 181 (accept_3_3 65 75 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 75 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 181
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 75 181 (accept_3_3 62 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 75 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 75 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 181 (accept_3_3 59 75 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 181 (accept_3_3 56 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 181 (Polychromatic418967fa.accept_16_7_11_5_1_4402 55 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 181 (accept_3_3 53 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 181 (accept_3_3 50 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 181 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 181 (accept_3_3 47 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 181 (accept_3_3 44 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 181 (accept_3_3 41 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 181 (accept_3_3 38 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 181 (Polychromatic418967fa.accept_13_11_10_12_1_1338 37 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 181 (accept_3_3 35 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 181 (accept_3_3 32 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 181 (accept_3_3 29 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 181
  (Polychromatic418967fa.accept_18_9_3_1_1_2559 27 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 181 (accept_3_3 26 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 181 (accept_3_3 23 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 181 (accept_3_3 20 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 181 (accept_3_3 17 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 181 (accept_3_3 14 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 181 (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 181 (accept_3_3 11 75 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 181
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 181 (accept_3_3 8 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 181 (accept_3_3 5 75 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 181 (Polychromatic418967fa.accept_21_3_12_13_1_8816
  3 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 181 (accept_3_3 2 75
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 181 (Polychromatic418967fa.accept_7_1_5_6_1_59
  1 75 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 181 (allA_of_3_1 74 74
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 181 (allA_succ_of_accept 72 73 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 181 (accept_3_3 71 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 181 (Polychromatic418967fa.accept_13_5_8_12_1_2759 70 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 181 (Polychromatic418967fa.accept_13_4_8_12_1_3526 69 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 181 (accept_3_3 68 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 73 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 181
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 66 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 181 (accept_3_3 65 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 181 (Polychromatic418967fa.accept_11_9_7_5_1_749 64 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 181 (Polychromatic418967fa.accept_15_3_13_1_1_479 63 73 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 181 (accept_3_3 62 73 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 181 (Polychromatic418967fa.accept_13_9_8_12_1_2031 61 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 181 (accept_3_3 59 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 181 (Polychromatic418967fa.accept_13_5_8_12_1_2759 57 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 181 (accept_3_3 56 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 73
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 181
  (Polychromatic418967fa.accept_20_14_13_1_1_8844 54 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 181 (accept_3_3 53 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 73 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 181 (accept_3_3 50 73 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 181 (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 181
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 181 (accept_3_3 47 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 181 (Polychromatic418967fa.accept_16_13_9_5_1_3302 45 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 181 (accept_3_3 44 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 181 (Polychromatic418967fa.accept_13_4_8_12_1_3526 43 73
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 181
  (Polychromatic418967fa.accept_10_2_3_1_1_481 42 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 181 (accept_3_3 41 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045 40 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 73 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 181 (accept_3_3 38 73 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 181
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 181 (accept_3_3 35 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 181 (Polychromatic418967fa.accept_20_14_13_1_1_8844 34 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 181 (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 181 (accept_3_3 32 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 181 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 73 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 181 (accept_3_3 29 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 181 (accept_3_3 26 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 181
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 181 (accept_3_3 23 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 181 (Polychromatic418967fa.accept_10_2_3_1_1_481 22 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 181 (Polychromatic418967fa.accept_24_21_1_13_1_6707 21 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 181 (accept_3_3 20 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 181 (Polychromatic418967fa.accept_23_19_4_20_1_10394 19 73
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 181 (accept_3_3 17 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 181 (Polychromatic418967fa.accept_17_15_5_11_1_6468 15 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 181 (accept_3_3 14 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 181 (Polychromatic418967fa.accept_16_13_9_5_1_3302 13 73
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 181
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 181 (accept_3_3 11 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 181 (Polychromatic418967fa.accept_13_10_8_12_1_2032 10 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 181 (accept_3_3 8 73 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 181 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 73 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 181
  (Polychromatic418967fa.accept_17_6_5_11_1_4073 6 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 181 (accept_3_3 5 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 181 (Polychromatic418967fa.accept_15_3_13_1_1_479 3 73 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 181 (accept_3_3 2 73 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 73 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 181 (allA_succ_of_accept 71
  72 181 (accept_3_3 71 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 181
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 70 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 181 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 72 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 181 (accept_3_3 68 72 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 66
  72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 181 (accept_3_3 65 72
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 181 (Polychromatic418967fa.accept_7_1_2_6_1_55
  64 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 72 181
  (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 72 181 (accept_3_3 62 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  72 181 (Polychromatic418967fa.accept_16_13_8_5_1_3298 61 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 72 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 181 (accept_3_3 59 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 181 (Polychromatic418967fa.accept_13_6_7_12_1_3504 58 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 72 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 72 181 (accept_3_3 56 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  72 181 (Polychromatic418967fa.accept_19_17_15_10_1_8934 55 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 72 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 181 (accept_3_3 53 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 72 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 72 181
  (Polychromatic418967fa.accept_16_3_8_5_1_6790 51 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 72 181 (accept_3_3 50 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  72 181 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 72 181 (Polychromatic418967fa.accept_21_6_9_13_1_8780 48 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 181 (accept_3_3 47 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 72 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 72 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 72 181 (accept_3_3 44 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  72 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 72 181 (Polychromatic418967fa.accept_19_4_15_10_1_4602 42 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 181 (accept_3_3 41 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 181 (Polychromatic418967fa.accept_17_6_4_11_1_4072 40 72
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 72 181 (accept_3_3 38 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  72 181 (Polychromatic418967fa.accept_13_11_7_12_1_2758 37 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 72 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 181 (accept_3_3 35 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 72 181
  (Polychromatic418967fa.accept_10_3_2_1_1_839 33 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 72 181 (accept_3_3 32 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  72 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 72 181 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 181 (accept_3_3 29 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 181 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 72
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 181
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 27 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 72 181 (accept_3_3 26 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  72 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 72 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 181 (accept_3_3 23 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 72 181
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 72 181 (accept_3_3 20 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  72 181 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 72 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 181 (accept_3_3 17 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 72 181 (accept_3_3 14 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  72 181 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 72 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 181 (accept_3_3 11 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 181
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 72 181 (accept_3_3 8 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72
  181 (Polychromatic418967fa.accept_21_7_9_13_1_5612 7 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 72 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 181 (accept_3_3 5 72 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 72 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 181 (accept_3_3 2 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72
  181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 181
  (allA_of_3_1 71 71 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 181 (allA_succ_of_accept 69 70 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 181 (accept_3_3 68 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 181 (accept_3_3 65 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 181 (accept_3_3 62 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 181 (Polychromatic418967fa.accept_18_7_16_1_1_4951 61 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 181 (accept_3_3 59 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 181 (accept_3_3 56 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 181 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 181 (accept_3_3 53 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 181 (accept_3_3 50 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 181 (accept_3_3 47 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 181 (Polychromatic418967fa.accept_13_7_5_12_1_1305 46 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 181 (accept_3_3 44 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 181 (accept_3_3 41 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 181 (accept_3_3 38 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 181 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 181 (accept_3_3 35 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 181 (Polychromatic418967fa.accept_13_8_5_12_1_2755 34 70
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 181 (accept_3_3 32 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 181 (accept_3_3 29 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 181 (accept_3_3 26 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 181 (Polychromatic418967fa.accept_17_8_2_11_1_4069 25 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 181 (accept_3_3 23 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 181 (accept_3_3 20 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 181 (Polychromatic418967fa.accept_21_18_7_13_1_8801 18 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 181 (accept_3_3 17 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 70 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 181 (accept_3_3 14 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 181 (accept_3_3 11 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 181 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 70 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 181 (accept_3_3 8 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 70 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 181 (accept_3_3 5 70 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 70 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 181 (accept_3_3 2 70 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 181 (Polychromatic418967fa.accept_13_1_5_12_1_306 1
  70 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 181 (allA_succ_of_accept 68 69
  181 (accept_3_3 68 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 181
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 181 (accept_3_3 65 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 181 (Polychromatic418967fa.accept_11_8_3_5_1_355
  63 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 181 (accept_3_3 62
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 181
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 69 181 (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 181 (accept_3_3 59 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 57
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 181 (accept_3_3 56 69
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 181
  (Polychromatic418967fa.accept_10_5_9_1_1_187 55 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 69 181 (Polychromatic418967fa.accept_13_2_4_12_1_745 54 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 181 (accept_3_3 53 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 181 (Polychromatic418967fa.accept_12_3_9_1_1_290
  51 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 181 (accept_3_3 50
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 181
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 69 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 181 (accept_3_3 47 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 181 (Polychromatic418967fa.accept_10_5_9_1_1_187
  45 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 181 (accept_3_3 44
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 181
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 69 181 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 181 (accept_3_3 41 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 39
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 181 (accept_3_3 38 69
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 181
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 69 181 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 181 (accept_3_3 35 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 181 (Polychromatic418967fa.accept_13_7_4_12_1_1341
  33 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 181 (accept_3_3 32
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 181
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 69 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 181 (accept_3_3 29 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 181 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 181 (accept_3_3 26
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 181
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 69 181 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 181 (accept_3_3 23 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 181 (accept_3_3 20 69
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 181
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 69 181 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 181 (accept_3_3 17 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 181 (Polychromatic418967fa.accept_10_5_9_1_1_187
  15 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 181 (accept_3_3 14
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 181
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 69 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 181 (accept_3_3 11 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 181
  (Polychromatic418967fa.accept_19_9_12_10_1_10393 9 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 181 (accept_3_3 8 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 181 (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 181 (accept_3_3 5 69 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 69
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 181 (accept_3_3 2 69 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 181 (Polychromatic418967fa.accept_22_1_3_5_1_375 1
  69 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 181 (allA_of_3_1 68 68 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 181 (allA_succ_of_accept 66 67 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 181 (accept_3_3 65 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 181 (Polychromatic418967fa.accept_10_4_7_1_1_471 64 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 181 (Polychromatic418967fa.accept_17_12_16_11_1_7885 63 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 181 (accept_3_3 62 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 67 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 181 (accept_3_3 59 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 181 (accept_3_3 56 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 181 (Polychromatic418967fa.accept_13_3_2_12_1_2797 55 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 181 (accept_3_3 53 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 181 (accept_3_3 50 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 181 (Polychromatic418967fa.accept_13_10_2_12_1_1332 49 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 181 (accept_3_3 47 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 181 (accept_3_3 44 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 181 (accept_3_3 41 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 181 (accept_3_3 38 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 181
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 181 (accept_3_3 35 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 181 (accept_3_3 32 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 181 (accept_3_3 29 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 181 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 181 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 181 (accept_3_3 26 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 181 (accept_3_3 23 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 181 (accept_3_3 20 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 181 (accept_3_3 17 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 181 (accept_3_3 14 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 181 (Polychromatic418967fa.accept_25_13_17_6_1_10392 13 67 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 181 (accept_3_3 11 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 181 (accept_3_3 8 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 181 (accept_3_3 5 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  181 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 67 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 67 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 181 (accept_3_3 2 67 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 181 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 67 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 181 (allA_succ_of_accept 65 66
  181 (accept_3_3 65 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 181
  (Polychromatic418967fa.accept_17_13_15_11_1_2936 64 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 181 (accept_3_3 62 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 66 181 (accept_3_3 59 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  66 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 66 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 57 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 181 (accept_3_3 56 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 181
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 66 181 (accept_3_3 53 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  66 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 181 (accept_3_3 50 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 181
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 181 (accept_3_3 47 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  66 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 181 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 181 (accept_3_3 44 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 181 (accept_3_3 41 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  66 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 181 (accept_3_3 38 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 181
  (Polychromatic418967fa.accept_20_16_6_1_1_7270 36 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 181 (accept_3_3 35 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 181 (accept_3_3 32 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 181 (accept_3_3 29 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 181 (Polychromatic418967fa.accept_13_2_1_12_1_1326 28 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 181 (accept_3_3 26 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 181 (accept_3_3 23 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 181 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 181 (accept_3_3 20 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 181 (accept_3_3 17 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 181 (accept_3_3 14 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 181
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 181 (accept_3_3 11 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 181 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 181 (accept_3_3 8 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 181 (accept_3_3 5 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 66 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 181 (accept_3_3 2 66 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 181 (Polychromatic418967fa.accept_19_1_9_10_1_10391 1 66 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 181 (allA_of_3_1 65 65 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 181 (allA_succ_of_accept 63 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 181 (accept_3_3 62 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 181 (Polychromatic418967fa.accept_19_3_7_10_1_6023 60 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 181 (accept_3_3 59 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 64 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 181 (accept_3_3 56 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 181 (accept_3_3 53 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 181 (Polychromatic418967fa.accept_18_16_10_1_1_3696 52 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 181 (accept_3_3 50 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 181 (Polychromatic418967fa.accept_14_7_8_13_1_3161 49 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 181 (Polychromatic418967fa.accept_15_3_4_1_1_1072 48 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 181 (accept_3_3 47 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 181 (accept_3_3 44 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 181 (Polychromatic418967fa.accept_19_5_7_10_1_7375 43 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 181 (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 181 (accept_3_3 41 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 64 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 181 (accept_3_3 38 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 181 (Polychromatic418967fa.accept_19_17_7_10_1_1171 36 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 181 (accept_3_3 35 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 64
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 181 (accept_3_3 32 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 181 (Polychromatic418967fa.accept_18_13_10_1_1_9025 31 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 181 (accept_3_3 29 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 181 (Polychromatic418967fa.accept_19_9_7_10_1_1170 28 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 181 (accept_3_3 26 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 181 (Polychromatic418967fa.accept_17_7_13_11_1_2895 24 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 181 (accept_3_3 23 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 64
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 181 (accept_3_3 20 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 181 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 181 (accept_3_3 17 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 181 (accept_3_3 14 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 181 (Polychromatic418967fa.accept_18_13_10_1_1_9025 13 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 181 (accept_3_3 11 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 181 (accept_3_3 8 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  181 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 64 181 (Polychromatic418967fa.accept_17_6_13_11_1_995 6 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 181 (accept_3_3 5 64 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 181 (Polychromatic418967fa.accept_21_4_1_13_1_8751 4 64 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 181 (accept_3_3 2 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  181 (Polychromatic418967fa.accept_19_1_7_10_1_8926 1 64 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 64 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 181
  (allA_succ_of_accept 62 63 181 (accept_3_3 62 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 181 (Polychromatic418967fa.accept_19_4_6_10_1_7396 61 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 181 (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 181 (accept_3_3 59 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 181
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 181 (accept_3_3 56 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 181 (Polychromatic418967fa.accept_24_7_15_13_1_8570 55 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 181 (accept_3_3 53 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 181
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 181 (accept_3_3 50 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 181 (Polychromatic418967fa.accept_13_10_11_12_1_1320 49 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 181 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 181 (accept_3_3 47 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 181 (accept_3_3 44 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 181 (Polychromatic418967fa.accept_13_4_11_12_1_1318 43 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 181 (accept_3_3 41 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 181
  (Polychromatic418967fa.accept_18_3_9_1_1_3690 39 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 181 (accept_3_3 38 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 181 (Polychromatic418967fa.accept_23_14_17_20_1_8624 37 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 181 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 181 (accept_3_3 35 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 181 (accept_3_3 32 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 181 (Polychromatic418967fa.accept_17_14_12_11_1_4063 31 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 181 (accept_3_3 29 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 181
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 181 (accept_3_3 26 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 181 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 181 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 181 (accept_3_3 23 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 181 (accept_3_3 20 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 181 (Polychromatic418967fa.accept_15_4_3_1_1_487 19 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 181 (accept_3_3 17 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 181
  (Polychromatic418967fa.accept_14_1_7_13_1_333 15 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 181 (accept_3_3 14 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 181 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 181 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 181 (accept_3_3 11 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 181 (accept_3_3 8 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  181 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 181 (accept_3_3 5 63 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 181
  (Polychromatic418967fa.accept_11_3_8_5_1_336 3 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 181 (accept_3_3 2 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  181 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 63 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 181
  (allA_of_3_1 62 62 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 181 (allA_succ_of_accept 60 61 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 181 (accept_3_3 59 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 181 (accept_3_3 56 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 181 (Polychromatic418967fa.accept_13_3_9_12_1_2062 55 61 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 181
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 181 (accept_3_3 53 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 181 (Polychromatic418967fa.accept_17_1_10_11_1_2943 52 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 181 (accept_3_3 50 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 181 (accept_3_3 47 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 181 (accept_3_3 44 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 61 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 181 (accept_3_3 41 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 181 (accept_3_3 38 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 181 (Polychromatic418967fa.accept_17_3_10_11_1_7848 37 61 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 181 (accept_3_3 35 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 181 (accept_3_3 32 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 61 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 181 (accept_3_3 29 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 181 (Polychromatic418967fa.accept_19_9_4_10_1_7370 28 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 181 (Polychromatic418967fa.accept_19_8_4_10_1_7393 27 61 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 181 (accept_3_3 26 61 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 181 (accept_3_3 23 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 181 (accept_3_3 20 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 181 (Polychromatic418967fa.accept_22_19_17_5_1_10390 19 61 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 181 (accept_3_3 17 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 181 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 181 (accept_3_3 14 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 61 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 181 (accept_3_3 11 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 181 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 181 (accept_3_3 8 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 181 (Polychromatic418967fa.accept_21_7_19_13_1_7164 7 61 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 181 (accept_3_3 5 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 61 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 181 (accept_3_3 2 61 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 181 (allA_succ_of_accept 59 60 181 (accept_3_3 59 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 60 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 60 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 181 (accept_3_3 56 60 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 181 (Polychromatic418967fa.accept_16_7_12_5_1_734
  55 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 181 (accept_3_3 53 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 181 (accept_3_3 50 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 181 (accept_3_3 47 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 181 (Polychromatic418967fa.accept_13_7_8_12_1_2810 46 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 181 (accept_3_3 44 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 181
  (Polychromatic418967fa.accept_16_10_12_5_1_2254 42 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 181 (accept_3_3 41 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 181 (accept_3_3 38 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 181
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 181 (accept_3_3 35 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 181 (accept_3_3 32 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 181 (accept_3_3 29 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 181 (Polychromatic418967fa.accept_19_9_3_10_1_6017 28 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 181 (accept_3_3 26 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 181 (accept_3_3 23 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 181 (accept_3_3 20 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 181
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 181 (accept_3_3 17 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 181 (Polychromatic418967fa.accept_19_15_3_10_1_10389 15 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 181 (accept_3_3 14 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 60 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 181 (accept_3_3 11 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 181 (accept_3_3 8 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 181
  (Polychromatic418967fa.accept_21_6_18_13_1_8767 6 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 181 (accept_3_3 5 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  181 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 60 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 181 (accept_3_3 2 60 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 60 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 181 (allA_of_3_1 59 59 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 181
  (allA_succ_of_accept 57 58 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 181 (accept_3_3 56 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 181 (Polychromatic418967fa.accept_13_2_6_12_1_1334
  54 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 181 (accept_3_3 53
  58 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 52 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 181 (accept_3_3 50 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 48
  58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 181 (accept_3_3 47 58
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 46 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 181 (accept_3_3 44 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 42
  58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 181 (accept_3_3 41 58
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 181
  (Polychromatic418967fa.accept_12_4_10_1_1_706 40 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 181 (accept_3_3 38 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 58 181 (Polychromatic418967fa.accept_20_17_18_1_1_8880 37 58 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 181 (accept_3_3 35 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 181 (accept_3_3 32 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 181 (accept_3_3 29 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 181 (accept_3_3 26 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 58 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 181 (accept_3_3 23 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 181 (accept_3_3 20 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 181 (accept_3_3 17 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 181 (accept_3_3 14 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 58 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 181 (accept_3_3 11 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 181 (accept_3_3 8 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 181 (accept_3_3 5 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 58 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 181 (accept_3_3 2 58 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 58 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 181 (allA_succ_of_accept 56 57 181 (accept_3_3 56 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 181 (Polychromatic418967fa.accept_17_4_6_11_1_1030 55 57 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 57 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 181 (accept_3_3 53 57 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 181 (accept_3_3 50 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  57 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 181 (Polychromatic418967fa.accept_18_12_3_1_1_3685 48 57 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 181 (accept_3_3 47 57 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 181
  (Polychromatic418967fa.accept_13_6_5_12_1_307 45 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 57 181 (accept_3_3 44 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  57 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 181 (accept_3_3 41 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 181 (accept_3_3 38 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  57 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 181 (accept_3_3 35 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 181 (accept_3_3 32 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 181 (accept_3_3 29 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 181 (accept_3_3 26 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 181 (accept_3_3 23 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 181
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 181 (accept_3_3 20 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 181 (Polychromatic418967fa.accept_20_18_17_1_1_10388 18 57 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 181 (accept_3_3 17 57 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 181 (accept_3_3 14 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 181 (accept_3_3 11 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 181 (accept_3_3 8 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 57 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 181 (accept_3_3 5 57 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 181 (accept_3_3 2 57 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 181 (Polychromatic418967fa.accept_13_1_5_12_1_306 1
  57 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 181 (allA_of_3_1 56 56 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 181 (allA_succ_of_accept 54 55 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 181 (accept_3_3 53 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 181 (Polychromatic418967fa.accept_15_6_10_1_1_3675 51 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 181 (accept_3_3 50 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 55 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 181
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 48 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 181 (accept_3_3 47 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 181 (Polychromatic418967fa.accept_19_7_17_10_1_4630 45 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 181 (accept_3_3 44 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 181 (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 55
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 181 (accept_3_3 41 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 181 (Polychromatic418967fa.accept_17_6_4_11_1_4072 40 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 55 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 181 (accept_3_3 38 55 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 181
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 181 (accept_3_3 35 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 181 (Polychromatic418967fa.accept_23_10_9_20_1_10387 33 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 181 (accept_3_3 32 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 181 (Polychromatic418967fa.accept_19_12_17_10_1_7365 31 55
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 181 (accept_3_3 29 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 181 (Polychromatic418967fa.accept_13_2_3_12_1_735 28 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 181 (Polychromatic418967fa.accept_16_11_7_5_1_4364 27 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 181 (accept_3_3 26 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 181 (Polychromatic418967fa.accept_20_5_15_1_1_7278 25 55
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 181
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 181 (accept_3_3 23 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 181 (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 181 (accept_3_3 20 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 55 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 181 (accept_3_3 17 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 181 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 181 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 55 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 181 (accept_3_3 14 55 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 181 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 181
  (Polychromatic418967fa.accept_16_12_7_5_1_1412 12 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 181 (accept_3_3 11 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 55 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 181 (accept_3_3 8 55 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 55 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 181 (accept_3_3 5 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  181 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 55 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 181 (Polychromatic418967fa.accept_25_3_5_6_1_10386 3 55 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 181 (accept_3_3 2 55 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 181 (Polychromatic418967fa.accept_19_1_17_10_1_4689 1 55 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 181)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 181 (allA_succ_of_accept 53 54 181 (accept_3_3 53 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 181 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 54 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 181 (accept_3_3 50 54 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 181
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 49 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 54 181 (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 54 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 181 (accept_3_3 47 54 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 54 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 54 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 54 181 (Polychromatic418967fa.accept_10_5_4_1_1_842
  45 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 181 (accept_3_3 44
  54 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 54 181 (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 54 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 181 (accept_3_3 41 54 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 54 181 (Polychromatic418967fa.accept_13_1_2_12_1_1299 40 54 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 54 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 54 181 (accept_3_3 38 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  54 181 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 54 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 54 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 181 (accept_3_3 35 54 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 181 (Polychromatic418967fa.accept_14_6_12_13_1_3180 34 54 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 181
  (Polychromatic418967fa.accept_16_1_6_5_1_4385 33 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 54 181 (accept_3_3 32 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  54 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 54 181 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 54 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 181 (accept_3_3 29 54 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 181 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 54 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 54 181 (accept_3_3 26 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  54 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 54 181 (Polychromatic418967fa.accept_19_5_16_10_1_7384 24 54 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 181 (accept_3_3 23 54 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 54 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 181
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 54 181 (accept_3_3 20 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  54 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 54 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 54 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 181 (accept_3_3 17 54 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 181 (Polychromatic418967fa.accept_13_3_2_12_1_2797 16 54 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 54 181 (accept_3_3 14 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  54 181 (Polychromatic418967fa.accept_19_13_16_10_1_6016 13 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 54 181 (Polychromatic418967fa.accept_23_12_8_20_1_10385 12 54 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 181 (accept_3_3 11 54 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 181 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 54
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 181
  (Polychromatic418967fa.accept_17_9_3_11_1_3983 9 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 54 181 (accept_3_3 8 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54
  181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 54 181 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 54 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 181 (accept_3_3 5 54 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 54 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 54 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 181 (accept_3_3 2 54 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  181)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 181 (allA_of_3_1 53 53 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 181 (allA_succ_of_accept 51 52 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 181 (accept_3_3 50 52 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 49
  52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 181 (accept_3_3 47 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 181 (accept_3_3 44 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 181 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 52 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 181 (accept_3_3 41 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 181 (accept_3_3 38 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 181
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 181 (accept_3_3 35 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 181 (accept_3_3 32 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 181 (accept_3_3 29 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 181 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 181 (accept_3_3 26 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 181 (accept_3_3 23 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 181 (accept_3_3 20 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 181 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 52 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 181 (accept_3_3 17 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 181 (accept_3_3 14 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 52 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 181 (accept_3_3 11 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 181 (accept_3_3 8 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 181 (Polychromatic418967fa.accept_17_7_1_11_1_1894 7 52 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 181 (accept_3_3 5 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 52 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 181 (accept_3_3 2 52 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 52 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 181))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 181 (allA_succ_of_accept 50 51 181 (accept_3_3 50 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 51 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 51 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 181 (accept_3_3 47 51 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 181 (accept_3_3 44 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 181 (accept_3_3 41 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 181 (accept_3_3 38 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 181 (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 181 (accept_3_3 35 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 181 (accept_3_3 32 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 181 (accept_3_3 29 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 181
  (Polychromatic418967fa.accept_20_7_11_1_1_5840 27 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 181 (accept_3_3 26 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 181 (accept_3_3 23 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 181 (accept_3_3 20 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 181 (Polychromatic418967fa.accept_29_19_22_7_1_10384 19 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 181 (accept_3_3 17 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 181 (accept_3_3 14 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 181 (accept_3_3 11 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 181
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 181 (accept_3_3 8 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 51 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 181 (accept_3_3 5 51 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 181 (accept_3_3 2 51 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 51
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  181))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 181 (allA_of_3_1 50 50 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 181 (allA_succ_of_accept 48 49 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 181 (accept_3_3 47 49 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 181
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 46 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 49 181 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 49 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 181 (accept_3_3 44 49 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 49 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 42
  49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 181 (accept_3_3 41 49
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 181
  (Polychromatic418967fa.accept_19_2_11_10_1_10383 40 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 181 (accept_3_3 38 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 181 (Polychromatic418967fa.accept_13_11_10_12_1_1338 37 49 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 181
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 181 (accept_3_3 35 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 181 (accept_3_3 32 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 181 (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 49 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 181 (accept_3_3 29 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 181 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 49 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 181 (accept_3_3 26 49 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 181 (accept_3_3 23 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 181 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 181 (accept_3_3 20 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 181 (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 49 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 181
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 181 (accept_3_3 17 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 181 (accept_3_3 14 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 181 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 49 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 181
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 181 (accept_3_3 11 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 181 (Polychromatic418967fa.accept_18_10_13_1_1_7736 10 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 181 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 181 (accept_3_3 8 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 181 (accept_3_3 5 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  181 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 49 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 49 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 181 (accept_3_3 2 49 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 181 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 49 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 181))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 181 (allA_succ_of_accept 47 48 181 (accept_3_3 47 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 181 (Polychromatic418967fa.accept_17_12_14_11_1_998 46 48 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 181 (Polychromatic418967fa.accept_21_3_6_13_1_8756 45 48
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 181 (accept_3_3 44 48 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 43
  48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 181 (accept_3_3 41 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 181 (accept_3_3 38 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 181 (Polychromatic418967fa.accept_17_3_14_11_1_5243 37 48 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 181
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 181 (accept_3_3 35 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 181 (accept_3_3 32 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 181
  (Polychromatic418967fa.accept_21_9_6_13_1_8777 30 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 181 (accept_3_3 29 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 181 (Polychromatic418967fa.accept_15_13_3_1_1_3740 28 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 181 (Polychromatic418967fa.accept_20_7_8_1_1_5856 27 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 181 (accept_3_3 26 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 48 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 181 (accept_3_3 23 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 181 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 181 (accept_3_3 20 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 48 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 181
  (Polychromatic418967fa.accept_20_18_8_1_1_10382 18 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 181 (accept_3_3 17 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 181 (accept_3_3 14 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 181
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 181 (accept_3_3 11 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 181 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 181 (accept_3_3 8 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 181 (accept_3_3 5 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  181 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 48 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 48 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 181 (accept_3_3 2 48 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 181 (Polychromatic418967fa.accept_22_1_4_5_1_7074 1 48 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 181)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 181 (allA_of_3_1 47 47 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 181 (allA_succ_of_accept 45 46
  181 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 181 (accept_3_3 44 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 46 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 181 (accept_3_3 41 46 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 46 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 181 (accept_3_3 38 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 181 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 46 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 181 (accept_3_3 35 46 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 181 (Polychromatic418967fa.accept_13_8_7_12_1_3637 34 46
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 181 (accept_3_3 32 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 46 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 181 (accept_3_3 29 46 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 46 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 181 (accept_3_3 26 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 181 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 46 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 181 (accept_3_3 23 46 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 46 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 181 (accept_3_3 20 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 181 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 46 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 181 (accept_3_3 17 46 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 46 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 181 (accept_3_3 14 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 181 (Polychromatic418967fa.accept_17_13_12_11_1_2947 13 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 46 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 181 (accept_3_3 11 46 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 46 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 181 (accept_3_3 8 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 181 (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 46 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 181 (accept_3_3 5 46 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 46 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 181 (accept_3_3 2 46 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 181 (Polychromatic418967fa.accept_21_1_4_13_1_7128
  1 46 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  181)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 181 (allA_succ_of_accept 44 45 181 (accept_3_3 44 45
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 181
  (Polychromatic418967fa.accept_19_5_7_10_1_7375 43 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 181 (Polychromatic418967fa.accept_16_10_13_5_1_3292 42 45 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 181 (accept_3_3 41 45 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 39
  45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 181 (accept_3_3 38 45
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 181 (Polychromatic418967fa.accept_7_2_3_6_1_4
  37 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 181
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 181 (accept_3_3 35 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 181 (Polychromatic418967fa.accept_13_7_6_12_1_2027 33 45 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 181 (accept_3_3 32 45 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 181 (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 45
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 181
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 181 (accept_3_3 29 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 181 (accept_3_3 26 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 45 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 181
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 181 (accept_3_3 23 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 181 (Polychromatic418967fa.accept_18_3_9_1_1_3690 21 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 181 (accept_3_3 20 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 45 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 181 (accept_3_3 17 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 181 (accept_3_3 14 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 181 (Polychromatic418967fa.accept_25_13_20_6_1_10381 13 45 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 181
  (Polychromatic418967fa.accept_21_12_3_13_1_7145 12 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 181 (accept_3_3 11 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 181 (accept_3_3 8 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 181 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 45 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 181
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 181 (accept_3_3 5 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 45 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 181 (accept_3_3 2 45 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 181 (Polychromatic418967fa.accept_16_1_13_5_1_2280 1 45 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 181))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  181 (allA_of_3_1 44 44 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 181 (allA_succ_of_accept 42 43 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 181 (accept_3_3 41 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 181 (accept_3_3 38 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 43 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 181
  (Polychromatic418967fa.accept_17_2_9_11_1_4057 36 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 181 (accept_3_3 35 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 181 (accept_3_3 32 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 43 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 181 (accept_3_3 29 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 181 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 181 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 43 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 181 (accept_3_3 26 43 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 43
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 181 (accept_3_3 23 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 181 (accept_3_3 20 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 181 (accept_3_3 17 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 181 (accept_3_3 14 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 43 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 181 (accept_3_3 11 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 181 (accept_3_3 8 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 181 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 43 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 181 (accept_3_3 5 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  181 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 43 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 181 (accept_3_3 2 43 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 181 (Polychromatic418967fa.accept_22_1_21_5_1_10380 1 43 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 181))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 181
  (allA_succ_of_accept 41 42 181 (accept_3_3 41 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 181 (accept_3_3 38 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 181 (Polychromatic418967fa.accept_22_15_20_5_1_10379 37 42 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 181
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 181 (accept_3_3 35 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 181 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 181 (accept_3_3 32 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 181 (accept_3_3 29 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 181 (Polychromatic418967fa.accept_13_2_3_12_1_735 28 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 181 (accept_3_3 26 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 181
  (Polychromatic418967fa.accept_23_1_19_20_1_932 24 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 181 (accept_3_3 23 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 181 (accept_3_3 20 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 181
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 181 (accept_3_3 17 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 181 (accept_3_3 14 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 42 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 181 (accept_3_3 11 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 181 (Polychromatic418967fa.accept_23_10_19_20_1_10378 10 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 181 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 181 (accept_3_3 8 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 181
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 181 (accept_3_3 5 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  181 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 42 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 181 (accept_3_3 2 42 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 181 (Polychromatic418967fa.accept_17_1_8_11_1_6471 1 42 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 181)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 181
  (allA_of_3_1 41 41 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 181 (allA_succ_of_accept 39 40 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 181 (accept_3_3 38 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 181 (Polychromatic418967fa.accept_13_11_1_12_1_742 37 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 181 (accept_3_3 35 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 40 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 181 (accept_3_3 32 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 181 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 181 (accept_3_3 29 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 181 (Polychromatic418967fa.accept_13_2_1_12_1_1326 28 40 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 181 (accept_3_3 26 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 181 (accept_3_3 23 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 40 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 181 (accept_3_3 20 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 181 (Polychromatic418967fa.accept_16_3_8_5_1_6790 19 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 181 (accept_3_3 17 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 40 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 181 (accept_3_3 14 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 181 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 181 (accept_3_3 11 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 40 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 181 (accept_3_3 8 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 40 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 181 (accept_3_3 5 40 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 40 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 181 (accept_3_3 2 40 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  181)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 181 (allA_succ_of_accept 38 39 181 (accept_3_3 38 39 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 37
  39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 181
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 181 (accept_3_3 35 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 181 (accept_3_3 32 39 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 39 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 181 (accept_3_3 29 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 181 (Polychromatic418967fa.accept_16_11_7_5_1_4364 27 39 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 181 (accept_3_3 26 39 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 39 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 181 (accept_3_3 23 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 39 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 181 (accept_3_3 20 39 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 181 (accept_3_3 17 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 181 (accept_3_3 14 39 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 39 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 181 (accept_3_3 11 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 181 (accept_3_3 8 39 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 39 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 181 (accept_3_3 5 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 181 (accept_3_3 2 39 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 39 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 181))))))))))))))))))))))))))))))))))))))) (allB_succ 38 181
  (allA_of_3_1 38 38 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 181 (allA_succ_of_accept 36 37 181
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 181 (accept_3_3 35 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 181 (Polychromatic418967fa.accept_10_4_7_1_1_471 34 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 181 (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 37 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 181 (accept_3_3 32 37 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 37 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 181
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 181 (accept_3_3 29 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 181 (Polychromatic418967fa.accept_19_9_18_10_1_7446 28 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 181 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 37 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 181 (accept_3_3 26 37 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 181 (accept_3_3 23 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 181 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 37 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 181 (accept_3_3 20 37 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 181 (Polychromatic418967fa.accept_17_2_3_11_1_2919 19 37 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 181 (accept_3_3 17 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 181 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 37 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 181 (accept_3_3 14 37 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 181 (Polychromatic418967fa.accept_27_13_10_19_1_10377 13 37 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 181
  (Polychromatic418967fa.accept_22_12_15_5_1_10376 12 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 37 181 (accept_3_3 11 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 37 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 37 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 181 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 37 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 181 (accept_3_3 8 37 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 181 (Polychromatic418967fa.accept_13_7_11_12_1_2051
  7 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 181
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 181 (accept_3_3 5 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 37 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 181 (accept_3_3 2 37 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 181))))))))))))))))))))))))))))))))))))) (allB_succ 36 181
  (allA_succ_of_accept 35 36 181 (accept_3_3 35 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 181 (Polychromatic418967fa.accept_13_8_10_12_1_1337 34 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 181 (accept_3_3 32 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 181 (Polychromatic418967fa.accept_16_15_4_5_1_1411 31 36 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 181 (accept_3_3 29 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 181 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 181 (accept_3_3 26 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 36 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 181
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 36 181 (accept_3_3 23 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 181 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 181 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 36
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 181 (accept_3_3 20 36 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 19
  36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 181
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 181 (accept_3_3 17 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 181 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 181 (accept_3_3 14 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 181 (Polychromatic418967fa.accept_22_13_14_5_1_5370 13 36 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 181 (accept_3_3 11 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 181 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 181 (accept_3_3 8 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 181
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 181 (accept_3_3 5 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  181 (Polychromatic418967fa.accept_19_4_17_10_1_4632 4 36 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 181 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 181 (accept_3_3 2 36 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 181)))))))))))))))))))))))))))))))))))) (allB_succ 35
  181 (allA_of_3_1 35 35 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 181 (allA_succ_of_accept 33 34 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 181 (accept_3_3 32 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 34 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 181 (accept_3_3 29 34 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 181 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 34 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 181 (accept_3_3 26 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 34 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 181 (accept_3_3 23 34 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 34 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 181 (accept_3_3 20 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 181 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 34 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 181 (accept_3_3 17 34 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 34 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 181 (accept_3_3 14 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 34 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 181 (accept_3_3 11 34 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 181 (Polychromatic418967fa.accept_13_10_8_12_1_2032 10 34 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 181 (accept_3_3 8 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 34 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 181 (accept_3_3 5 34 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 34 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 181 (accept_3_3 2 34 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  1 34 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34
  181)))))))))))))))))))))))))))))))))) (allB_succ 33 181 (allA_succ_of_accept 32 33 181 (accept_3_3 32 33 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 33 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 181 (accept_3_3 29 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 33 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 181 (accept_3_3 26 33 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 181
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 181 (accept_3_3 23 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 181 (accept_3_3 20 33 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 181 (Polychromatic418967fa.accept_13_6_7_12_1_3504 19 33 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 181 (accept_3_3 17 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 181 (accept_3_3 14 33 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 33 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 181
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 181 (accept_3_3 11 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 181 (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 33 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 181 (accept_3_3 8 33 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 33 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 181
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 181 (accept_3_3 5 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 33 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 181 (accept_3_3 2 33 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 181))))))))))))))))))))))))))))))))) (allB_succ 32 181
  (allA_of_3_1 32 32 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 181 (allA_succ_of_accept 30 31 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 181 (accept_3_3 29 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 181 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 181 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 31 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 181 (accept_3_3 26 31 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 181 (accept_3_3 23 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 31 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 181 (accept_3_3 20 31 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 181 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 31 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 181 (accept_3_3 17 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 31 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 181 (accept_3_3 14 31 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 181 (Polychromatic418967fa.accept_27_13_4_19_1_10375 13 31 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 181 (accept_3_3 11 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 31 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 181 (accept_3_3 8 31 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 181 (accept_3_3 5 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 31 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 181 (accept_3_3 2 31 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 181 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 31 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 181))))))))))))))))))))))))))))))) (allB_succ 30 181
  (allA_succ_of_accept 29 30 181 (accept_3_3 29 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 181 (Polychromatic418967fa.accept_13_2_4_12_1_745 28 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 181 (accept_3_3 26 30 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 30 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 181 (accept_3_3 23 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 181 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 30 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 181 (accept_3_3 20 30 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 181 (accept_3_3 17 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 181 (accept_3_3 14 30 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 30 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 181
  (Polychromatic418967fa.accept_17_12_13_11_1_2910 12 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 30 181 (accept_3_3 11 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 30 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 181 (Polychromatic418967fa.accept_16_9_14_5_1_2239 9 30 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 181 (accept_3_3 8 30 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 181 (accept_3_3 5 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 30 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 181 (accept_3_3 2 30 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 181)))))))))))))))))))))))))))))) (allB_succ 29 181 (allA_of_3_1
  29 29 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 181 (allA_succ_of_accept 27 28 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 181 (accept_3_3 26 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 181 (Polychromatic418967fa.accept_16_8_12_5_1_200 24 28 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 181 (accept_3_3 23 28 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 28 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 181 (accept_3_3 20 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 181 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 28 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 181 (accept_3_3 17 28 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 181 (Polychromatic418967fa.accept_13_3_2_12_1_2797 16 28
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 181 (accept_3_3 14 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 28 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 181 (accept_3_3 11 28 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 28 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 181 (accept_3_3 8 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  181 (Polychromatic418967fa.accept_16_7_12_5_1_734 7 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 28 181 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 28 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 181 (accept_3_3 5 28 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 181 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 28 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 181 (accept_3_3 2 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 28 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 181)))))))))))))))))))))))))))) (allB_succ 27 181 (allA_succ_of_accept 26 27 181 (accept_3_3 26 27 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 181 (Polychromatic418967fa.accept_16_9_11_5_1_2279
  25 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 181
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 181 (accept_3_3 23 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 181 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 181 (accept_3_3 20 27 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 181 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 27 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 181 (accept_3_3 17 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 181 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 27 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 181 (accept_3_3 14 27 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 181 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 27
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 181
  (Polychromatic418967fa.accept_19_12_8_10_1_8948 12 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 181 (accept_3_3 11 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 181 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 27 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 181 (accept_3_3 8 27 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 181 (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 27 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 181 (accept_3_3 5 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 27 181 (Polychromatic418967fa.accept_17_3_10_11_1_7848 3 27 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 181 (accept_3_3 2 27 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 27 181 (Polychromatic418967fa.accept_17_1_10_11_1_2943 1 27 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 181))))))))))))))))))))))))))) (allB_succ 26 181 (allA_of_3_1 26
  26 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 181 (allA_succ_of_accept 24 25 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 181 (accept_3_3 23 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 25 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 181 (accept_3_3 20 25 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 25 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 181
  (Polychromatic418967fa.accept_17_1_8_11_1_6471 18 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 181 (accept_3_3 17 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 181 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 25 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 181 (accept_3_3 14 25 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 25 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 181 (accept_3_3 11 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 181 (accept_3_3 8 25 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 25 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 181 (accept_3_3 5 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  181 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 25 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 25 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 181 (accept_3_3 2 25 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 181 (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 25 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 181))))))))))))))))))))))))) (allB_succ 24 181
  (allA_succ_of_accept 23 24 181 (accept_3_3 23 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  24 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 24 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 181 (accept_3_3 20 24 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 181 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 24 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 181 (accept_3_3 17 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 24 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 181 (accept_3_3 14 24 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 24 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 181 (accept_3_3 11 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 181 (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 181 (accept_3_3 8 24 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 181
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 181 (accept_3_3 5 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 24 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 181 (accept_3_3 2 24 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 181 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 24 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 181)))))))))))))))))))))))) (allB_succ 23 181 (allA_of_3_1 23 23
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 181 (allA_succ_of_accept 21 22 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 181 (accept_3_3 20 22 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 181 (Polychromatic418967fa.accept_31_18_22_26_1_10374 18 22 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 181 (accept_3_3 17 22 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 22 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 181 (accept_3_3 14 22 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 181 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 22 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 22 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 181 (accept_3_3 11 22 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 181 (Polychromatic418967fa.accept_13_10_9_12_1_2814 10 22 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 181 (accept_3_3 8 22 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 22 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 181 (accept_3_3 5 22 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 22 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 181 (accept_3_3 2 22 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 181 (Polychromatic418967fa.accept_16_1_6_5_1_4385 1
  22 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 181)))))))))))))))))))))) (allB_succ
  21 181 (allA_succ_of_accept 20 21 181 (accept_3_3 20 21 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 181 (Polychromatic418967fa.accept_25_19_21_6_1_10373 19 21 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 181 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 21
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 181 (accept_3_3 17 21 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  21 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 181 (accept_3_3 14 21 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 21 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 181 (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 21 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 181 (accept_3_3 11 21 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 181
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 21 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 181 (accept_3_3 8 21 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 21 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 181 (accept_3_3 5 21 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  21 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 181 (accept_3_3 2 21 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  1 21 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 181))))))))))))))))))))) (allB_succ
  20 181 (allA_of_3_1 20 20 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 181 (allA_succ_of_accept 18 19
  181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 181 (accept_3_3 17 19 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 181 (Polychromatic418967fa.accept_21_16_19_13_1_7140 16 19 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 181 (accept_3_3 14 19 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 181 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 19 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 181
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 19 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 181 (accept_3_3 11 19 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 181 (Polychromatic418967fa.accept_17_9_2_11_1_4042 9 19 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 181 (accept_3_3 8 19 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 181 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 19 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 181 (accept_3_3 5 19 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 181 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 19 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 181 (accept_3_3 2 19 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 181))))))))))))))))))) (allB_succ 18 181 (allA_succ_of_accept 17
  18 181 (accept_3_3 17 18 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 18 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 181 (accept_3_3 14 18 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 18 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 12
  18 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 181 (accept_3_3 11 18
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 10 18 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 181 (accept_3_3 8 18 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 181 (Polychromatic418967fa.accept_13_6_5_12_1_307 6
  18 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 181 (accept_3_3 5 18 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 181 (Polychromatic418967fa.accept_13_4_5_12_1_751 4
  18 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 181 (accept_3_3 2 18 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  181 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 18 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 18 181)))))))))))))))))) (allB_succ 17 181 (allA_of_3_1 17 17 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 16 181 (allA_succ_of_accept 15 16 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 181 (accept_3_3 14 16 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  16 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 16 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 181 (accept_3_3 11 16 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 16 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 181 (accept_3_3 8 16 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 181 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 16 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 16 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 181 (accept_3_3 5 16 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 16 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 181 (accept_3_3 2 16 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 181)))))))))))))))) (allB_succ 15 181 (allA_succ_of_accept 14 15
  181 (accept_3_3 14 15 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 181
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 15 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 181 (accept_3_3 11 15 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9
  15 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 181 (accept_3_3 8 15 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7
  15 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 181 (accept_3_3 5 15 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 15 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 181 (accept_3_3 2 15 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 181 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 15 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 181))))))))))))))) (allB_succ 14 181 (allA_of_3_1 14 14 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 181 (allA_succ_of_accept 12 13 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 13 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 181 (accept_3_3 11 13 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 181 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 13 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 181 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 13 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 181 (accept_3_3 8 13 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 181 (accept_3_3 5 13 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  181 (Polychromatic418967fa.accept_19_4_13_10_1_7382 4 13 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 13 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 181 (accept_3_3 2 13 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 181 (Polychromatic418967fa.accept_16_1_13_5_1_2280 1 13 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 181))))))))))))) (allB_succ 12 181
  (allA_succ_of_accept 11 12 181 (accept_3_3 11 12 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  12 181 (Polychromatic418967fa.accept_16_10_12_5_1_2254 10 12 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 12 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 181 (accept_3_3 8 12 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 12 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 181 (accept_3_3 5 12 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12
  181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 12 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 12 181 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 12 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 181 (accept_3_3 2 12 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 12 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 181)))))))))))) (allB_succ 11 181 (allA_of_3_1 11 11 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 181 (allA_succ_of_accept 9 10 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 181 (accept_3_3 8 10 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 181 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 10 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 181 (accept_3_3 5 10 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 10 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 181 (accept_3_3 2 10 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 181 (Polychromatic418967fa.accept_17_1_10_11_1_2943
  1 10 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 181)))))))))) (allB_succ 9 181
  (allA_succ_of_accept 8 9 181 (accept_3_3 8 9 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 181
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 9 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 181 (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 9 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 181 (accept_3_3 5 9 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 181 (accept_3_3 2 9 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 181))))))))) (allB_succ 8 181
  (allA_of_3_1 8 8 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 181 (allA_succ_of_accept 6 7 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 181 (accept_3_3 5 7 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 181
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 7 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 181 (accept_3_3 2 7 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 181 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 7 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 181))))))) (allB_succ 6 181 (allA_succ_of_accept 5 6 181
  (accept_3_3 5 6 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 181
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 6 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 181 (accept_3_3 2 6 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 6 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 181)))))) (allB_succ 5 181 (allA_of_3_1 5 5 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 181 (allA_succ_of_accept 3 4 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 181 (accept_3_3 2 4 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 181
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 4 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 181)))) (allB_succ 3 181 (allA_succ_of_accept 2 3 181 (accept_3_3 2 3 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 181 (Polychromatic418967fa.accept_19_1_3_10_1_8917 1 3 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 181))) (allB_succ 2 181 (allA_of_3_1 2 2 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  181))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


