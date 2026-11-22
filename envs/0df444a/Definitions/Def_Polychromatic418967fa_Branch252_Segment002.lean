-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch252_Segment002
-- name    : Polychromatic418967fa_Branch252_Segment002
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:47:17.50808+00:00
-- url     : https://prove2.me/theorems/ada9407d-5768-4f60-bbe6-f662aaf70eea
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch252_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_252_segment_002 : allB 205 252 :=
  allB_succ' 49 204 252 (Eq.refl Bool.true) (allA_succ_of_gcd 48 204 252 12 4 17 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 204 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 204 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 204 252 2 23 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 204 252 3 15 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 204 252 4 11 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 204 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 43 204
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 204 252 6 7 34 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 204 252
  (Polychromatic418967fa.accept_13_2_9_5_1_959 41 204 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 204 252 4 10 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 204 252 3 13 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 204 252 2 19 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 204 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 204 252 12 3 17 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 204 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 35 204 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 204 252 2 17 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 204 252 3 11 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 204 252 4 8 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 204 252 (Polychromatic418967fa.accept_25_6_4_2_1_15395 31 204 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 252 6 5 34 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 29 204 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 204 252 4 7 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 204 252 3 9 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 204 252 2 13 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 204 252 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 204 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 252 12 2 17 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 252
  (Polychromatic418967fa.accept_25_23_4_2_1_15394 23 204 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 204 252 2 11 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 204 252 3 7 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 204 252 4 5 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 204 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 204 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 252 6 3 34 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 204 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 204 252 4 4 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 204 252 3 5 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 204 252 2 7 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 204 252 (Polychromatic418967fa.accept_19_13_14_5_1_8545 13 204 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 252 12 1 17 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 252
  (Polychromatic418967fa.accept_19_11_14_5_1_5629 11 204 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 204 252 2 5 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 204 252 3 3 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 204 252 4 2 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 204 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 204 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 252 6 1 34 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 204 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 252 4 1 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 204 252 3 1 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 204 252 2 1 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 204 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 252)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 203 252 (Eq.refl Bool.true) (allA_succ_of_gcd 49 203 252 7 7 29 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 203 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 48 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 203 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 203 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 203 252 (accept_3_4 46 203 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 203 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 203 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 203 252
  (Polychromatic418967fa.accept_24_20_11_12_1_15217 44 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 203 252 (accept_3_4 43 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 203 252 7 6 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 203 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 41 203 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 203 252 (accept_3_4 40 203 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 203 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 203 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 203 252 (Polychromatic418967fa.accept_13_12_8_5_1_976
  38 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 252 (accept_3_4 37
  203 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 252
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 203 252 7 5 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 203 252 (accept_3_4 34 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 252 (Polychromatic418967fa.accept_17_15_16_14_1_4291 32 203 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 252 (accept_3_4 31 203 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 252 (Polychromatic418967fa.accept_19_11_13_5_1_5714 30 203
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 252
  (Polychromatic418967fa.accept_13_3_8_5_1_974 29 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 203 252 7 4 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 203 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 203 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 203
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 252 (accept_3_4 25 203
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 252
  (Polychromatic418967fa.accept_16_8_11_12_1_962 24 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 203 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 203 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 252 (accept_3_4 22 203 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 203 252 7 3 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 203 252 (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 203 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 252 (accept_3_4 19 203 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 203
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 252 (accept_3_4 16 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 203 252 7 2 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 203 252 (accept_3_4 13 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 203 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 203 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 203
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 252 (accept_3_4 10 203
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 252
  (Polychromatic418967fa.accept_19_9_13_5_1_4351 9 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 203 252 (Polychromatic418967fa.accept_16_8_11_12_1_962 8 203 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 203 252 7 1 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 203 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 203 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 252 (accept_3_4 4 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 3 203 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 252 (Polychromatic418967fa.accept_17_2_16_14_1_2116 2 203 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 252 (accept_3_4 1 203 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 203 252)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 202
  252 (Eq.refl Bool.true) (allA_succ_of_gcd 50 202 252 2 25 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 202 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 49 202
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 202 252 2 24 101 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 202 252 (accept_3_5 47
  202 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 202 252 2 23 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 202 252
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 45 202 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 202 252 2 22 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 202 252 (Polychromatic418967fa.accept_16_11_10_12_1_4832 43 202 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 202 252 2 21 101 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 202 252 (accept_3_5 41
  202 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 202 252 2 20 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 202 252
  (Polychromatic418967fa.accept_19_1_12_5_1_11303 39 202 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 202 252 2 19 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 202 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 202 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 202 252 2 18 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 202 252 (accept_3_5 35 202 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 202 252 2 17 101 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 202 252
  (Polychromatic418967fa.accept_15_3_7_12_1_372 33 202 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 202 252 2 16 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 202 252 (Polychromatic418967fa.accept_26_5_20_18_1_15393 31 202 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 202 252 2 15 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 202 252 (accept_3_5 29 202 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 202 252 2 14 101 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 202 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 202 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 202 252 2 13 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 202 252 (Polychromatic418967fa.accept_13_12_7_5_1_3147 25 202 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 202 252 2 12 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 202 252 (accept_3_5 23 202 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 202 252 2 11 101 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 202 252
  (Polychromatic418967fa.accept_15_6_7_12_1_869 21 202 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 202 252 2 10 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 202 252 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 202 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 202 252 2 9 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 202 252 (accept_3_5 17 202 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 202 252 2 8 101 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 202 252
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 202 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 202 252 2 7 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 202 252 (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 202 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 202 252 2 6 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 202 252 (accept_3_5 11 202 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 202 252 2 5 101 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 202 252
  (Polychromatic418967fa.accept_19_9_12_5_1_5695 9 202 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 202 252 2 4 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 202 252 (Polychromatic418967fa.accept_19_7_12_5_1_7123 7 202 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 202 252 2 3 101 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 202 252 (accept_3_5 5 202 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 202 252 2 2 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 202 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 3
  202 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 252 2 1 101 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 252
  (Polychromatic418967fa.accept_19_1_12_5_1_11303 1 202 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 252))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 201 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 201 252 3 17 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 201 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 50 201 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 49 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 201 252 3 16 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 201 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 47 201 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 46 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 201 252 3 15 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 201 252 (Polychromatic418967fa.accept_19_6_11_5_1_5628 44 201 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 43 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 201 252 3 14 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 201 252 (Polychromatic418967fa.accept_23_18_17_22_1_15392 41 201 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 40 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 201 252 3 13 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 201 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 38 201 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 37 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 201 252 3 12 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 201 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 201 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 252
  (Polychromatic418967fa.accept_16_2_9_12_1_46 34 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 201 252 3 11 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 201 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 32 201 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 252
  (Polychromatic418967fa.accept_19_12_11_5_1_950 31 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 201 252 3 10 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 201 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 201 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 252
  (Polychromatic418967fa.accept_22_6_3_10_1_12182 28 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 201 252 3 9 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 201 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 201 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 252
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 201 252 3 8 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 201 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 23 201 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 252 (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 201
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 201 252 3 7 67 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 201 252
  (Polychromatic418967fa.accept_15_5_6_12_1_916 20 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 201 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 201 252 3 6 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 201 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333
  17 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 16 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 201 252 3 5 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 201 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 201 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 201 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 201 252 3 4 67 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 201 252
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 201 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 201 252 3 3 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 252 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 201 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 201 252 3 2 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 201 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 201 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 201 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 252 3 1 67 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 252
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 201 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 1 201 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 201 252)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  200 252 (Eq.refl Bool.true) (allA_succ_of_gcd 52 200 252 4 13 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 200 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 200
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 200 252 2 25 100 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 200 252 (accept_3_4 49
  200 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 200 252 4 12 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 200 252
  (Polychromatic418967fa.accept_15_2_5_12_1_369 47 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 200 252 2 23 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 200 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 200 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 200 252 4 11 50 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 200 252 (accept_3_4 43 200 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 200 252 2 21 100 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 200 252
  (Polychromatic418967fa.accept_16_9_8_12_1_979 41 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 200 252 4 10 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 200 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 200 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 200 252 2 19 100 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 200 252 (accept_3_4 37 200 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 200 252 4 9 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 200 252
  (Polychromatic418967fa.accept_16_3_8_12_1_2736 35 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 200 252 2 17 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 200 252 (Polychromatic418967fa.accept_16_1_8_12_1_405 33 200 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 200 252 4 8 50 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 200 252 (accept_3_4 31 200 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 200 252 2 15 100 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 200 252
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 29 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 200 252 4 7 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 200 252 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 200 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 200 252 2 13 100 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 200 252 (accept_3_4 25
  200 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 200 252 4 6 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 200 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 200 252 2 11 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 200 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 200 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 252 4 5 50 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 252 (accept_3_4 19 200 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 200 252 2 9 100 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 200 252
  (Polychromatic418967fa.accept_15_2_5_12_1_369 17 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 200 252 4 4 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 200 252 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 200 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 200 252 2 7 100 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 252 (accept_3_4 13 200 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 252 4 3 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 252
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 200 252 2 5 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 200 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 200 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 200 252 4 2 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 200 252 (accept_3_4 7 200 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200 252 2 3 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 200 252 (Polychromatic418967fa.accept_16_5_8_12_1_1766
  5 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 200 252 4 1 50 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 252
  (Polychromatic418967fa.accept_16_3_8_12_1_2736 3 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 252 2 1 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 252 (accept_3_4 1 200 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  252))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 199 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 199 252 (accept_3_5 53 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 199 252 (Polychromatic418967fa.accept_15_7_4_12_1_2530 52 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 199 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 199 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 252 (accept_3_5 50 199 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 49 199 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 252
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 48 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 252 (accept_3_5 47 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 46 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 252 (accept_3_5 44 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 199 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 42 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 252 (accept_3_5 41 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 40 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 252 (accept_3_5 38 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 199
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 252 (accept_3_5 35 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 252 (Polychromatic418967fa.accept_16_2_7_12_1_3793 34 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 199 252 (Polychromatic418967fa.accept_19_14_9_5_1_9941 33 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 252 (accept_3_5 32 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 199 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 252
  (Polychromatic418967fa.accept_23_7_15_22_1_15360 30 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 199 252 (accept_3_5 29 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 199 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 199 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 199 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 252 (accept_3_5 26 199 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 252
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 199 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 199 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 252 (accept_3_5 23 199 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 199 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 22 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 21 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 252 (accept_3_5 20 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 199 252 (Polychromatic418967fa.accept_16_2_7_12_1_3793 18 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 252 (accept_3_5 17 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 199
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 252
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 252 (accept_3_5 14 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 199 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 252 (accept_3_5 11 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 199
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 252 (accept_3_5 8 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 199 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 252 (accept_3_5 5 199 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 252 (Polychromatic418967fa.accept_16_4_7_12_1_2734 4 199 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 252 (accept_3_5 2 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 199 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 252)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 198 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 198 252 18 3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 198 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 53 198 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 198 252 2 26 99 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 198 252 3 17 66 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 198 252 2 25 99 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 198 252
  (Polychromatic418967fa.accept_24_1_6_12_1_8449 49 198 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 198 252 6 8 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 198 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 47 198 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 252 2 23 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 198 252 9 5 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 198 252 2 22 99 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 198 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 198 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 198 252 6 7 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 198 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 41 198 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 252 2 20 99 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 198 252 3 13 66 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 198 252 2 19 99 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 198 252
  (Polychromatic418967fa.accept_13_11_3_5_1_982 37 198 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 252 18 2 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 198 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 252 2 17 99 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 198 252 3 11 66 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 198 252 2 16 99 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 252
  (Polychromatic418967fa.accept_19_12_8_5_1_8538 31 198 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 252 6 5 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 198 252 (Polychromatic418967fa.accept_17_12_11_14_1_3120 29 198 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 252 2 14 99 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 198 252 9 3 22 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 198 252 2 13 99 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 198 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 252 6 4 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 198 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 198 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 252 2 11 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 198 252 3 7 66 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 198 252 2 10 99 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 252
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 198 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 252 18 1 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 198 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 252 2 8 99 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 198 252 3 5 66 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 198 252 2 7 99 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 198 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 198 252 6 2 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 198 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 198 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 252 2 5 99 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 198 252 9 1 22 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 198 252 2 4 99 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 198 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 252 6 1 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 198 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198 252 2 2 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 198 252 3 1 66 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 198 252 2 1 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 1
  198 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 197 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 197 252 (accept_3_4 55 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 197 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 197 252 (Polychromatic418967fa.accept_22_9_21_10_1_15292 53 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 252 (accept_3_4 52 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 51 197
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 252
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 50 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 197 252 (accept_3_4 49 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 197 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 48 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 197 252 (Polychromatic418967fa.accept_17_13_10_14_1_4211 47 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 252 (accept_3_4 46 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 197
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 252 (accept_3_4 43 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 197 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 252 (accept_3_4 40 197 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 252
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 38 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 252 (accept_3_4 37 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 252 (accept_3_4 34 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 197 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 252
  (Polychromatic418967fa.accept_19_13_7_5_1_5712 32 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 252 (accept_3_4 31 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 252 (accept_3_4 28 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 252 (Polychromatic418967fa.accept_20_7_17_12_1_11156 27
  197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 252
  (Polychromatic418967fa.accept_16_10_5_12_1_4925 26 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 197 252 (accept_3_4 25 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 197 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 197 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 197
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 252 (accept_3_4 22 197
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 252
  (Polychromatic418967fa.accept_15_6_2_12_1_885 21 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 197 252 (Polychromatic418967fa.accept_13_7_2_5_1_2344 20 197 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 252 (accept_3_4 19 197 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 197 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 197 252 (accept_3_4 16 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 252 (accept_3_4 13 197 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 197
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 252
  (Polychromatic418967fa.accept_22_11_21_10_1_5795 11 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 197 252 (accept_3_4 10 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 197 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 197 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 252 (Polychromatic418967fa.accept_16_8_5_12_1_3812 8 197
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 252 (accept_3_4 7 197 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 252 (Polychromatic418967fa.accept_15_6_2_12_1_885
  6 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 252 (accept_3_4 4 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 197 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 252 (Polychromatic418967fa.accept_19_2_7_5_1_3067 2 197 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 252 (accept_3_4 1 197 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 196 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 196 252 28 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 196 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 55 196 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 196 252 2 27 98 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 196 252 (accept_3_5 53 196 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 196 252 4 13 49 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 196 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 196 252 2 25 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 196 252 7 7 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 196 252 4 12 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 196 252 (accept_3_5 47 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 196 252 2 23 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 196 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 196 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 196 252 4 11 49 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 196 252
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 43 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 196 252 14 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 196 252 (accept_3_5 41 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 196 252 4 10 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 196 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 196 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 196 252 2 19 98 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 196 252
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 37 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 196 252 4 9 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 196 252 7 5 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 196 252 2 17 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 196 252 (Polychromatic418967fa.accept_16_1_4_12_1_376 33 196 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 196 252 4 8 49 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 196 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 196 252 2 15 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 196 252 (accept_3_5 29 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 196 252 28 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 196 252 (Polychromatic418967fa.accept_16_11_4_12_1_1760 27 196 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 196 252 2 13 98 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 196 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 196 252 4 6 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 196 252 (accept_3_5 23 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  196 252 2 11 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  21 196 252 7 3 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  20 196 252 4 5 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 196 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 196 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 196 252 2 9 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 196 252 (accept_3_5 17 196 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 196 252 4 4 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 196 252 (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 196
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 252 14 1 14 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 252
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 196 252 4 3 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 196 252 (accept_3_5 11 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 196 252 2 5 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 196 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 196 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 252 4 2 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 196 252 7 1 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 196 252 2 3 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 252 (accept_3_5 5 196 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 252 4 1 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 196 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 196 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 196 252 2 1 98 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 196 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 196 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 196 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 195 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 195 252 3 19 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 195 252 (Polychromatic418967fa.accept_16_8_3_12_1_1819 56 195 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 55 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 195 252 3 18 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 195 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 53 195 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 252
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 52 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 195 252 3 17 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 195 252 (Polychromatic418967fa.accept_17_16_8_14_1_6757 50 195 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 195 252
  (Polychromatic418967fa.accept_22_5_19_10_1_15391 49 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 195 252 3 16 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 195 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 195 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 252
  (Polychromatic418967fa.accept_20_6_15_12_1_6637 46 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 195 252 3 15 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 195 252 (Polychromatic418967fa.accept_25_19_20_2_1_15227 44 195 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 43 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 195 252 3 14 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 195 252 (Polychromatic418967fa.accept_16_9_3_12_1_1802 41 195 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 252
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 40 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 195 252 3 13 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 195 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 195 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 252 (Polychromatic418967fa.accept_10_7_5_2_1_880
  37 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 195 252 3 12 65 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 195 252
  (Polychromatic418967fa.accept_22_13_19_10_1_15251 35 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 195 252 (Polychromatic418967fa.accept_25_9_20_2_1_15200 34 195 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 195 252 3 11 65 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 195 252
  (Polychromatic418967fa.accept_25_7_20_2_1_15228 32 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 195 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 195 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 252 3 10 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 252
  (Polychromatic418967fa.accept_22_7_19_10_1_15352 29 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 195 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 195 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 195 252 3 9 65 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 195 252
  (Polychromatic418967fa.accept_16_10_3_12_1_1758 26 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 195 252 (Polychromatic418967fa.accept_16_9_3_12_1_1802 25 195 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 195 252 3 8 65 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 195 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 252 (Polychromatic418967fa.accept_25_22_20_2_1_15390 22 195 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 195 252 3 7 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 195 252
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 252 (Polychromatic418967fa.accept_23_19_11_22_1_15190 19 195 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 252 3 6 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 252 (Polychromatic418967fa.accept_17_16_8_14_1_6757 16 195 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 195 252 3 5 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 195 252
  (Polychromatic418967fa.accept_23_14_11_22_1_13704 14 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 195 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 195 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 195 252 3 4 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 195 252
  (Polychromatic418967fa.accept_17_11_8_14_1_8084 11 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 195 252 (Polychromatic418967fa.accept_16_10_3_12_1_1758 10 195 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 195 252 3 3 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 195 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 252 3 2 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 195 252 (Polychromatic418967fa.accept_20_5_15_12_1_9720 5 195
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 252
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 4 195 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 195 252 3 1 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 195 252 (Polychromatic418967fa.accept_23_2_11_22_1_15175 2 195 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 252 (Polychromatic418967fa.accept_22_1_19_10_1_15355 1 195
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 194 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 194 252 2 29 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 194 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 194 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 194 252 2 28 97 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 194 252 (accept_3_4 55 194 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 194 252 2 27 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 194 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601
  53 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 194 252 2 26 97 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 194 252
  (Polychromatic418967fa.accept_23_5_10_22_1_15244 51 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 194 252 2 25 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 194 252 (accept_3_4 49 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 194 252 2 24 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 194 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 194 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 194 252 2 23 97 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 194 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 194 252 2 22 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 194 252 (accept_3_4 43 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 252 2 21 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 252 (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 194 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 252 2 20 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 252
  (Polychromatic418967fa.accept_15_9_14_12_1_913 39 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 252 2 19 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 252 (accept_3_4 37 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 252 2 18 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 252 (Polychromatic418967fa.accept_23_12_10_22_1_8787 35 194 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 252 2 17 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 252
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 33 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 252 2 16 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 252 (accept_3_4 31 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 252 2 15 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 252 (Polychromatic418967fa.accept_27_2_5_9_1_3548 29 194 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 252 2 14 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 252 2 13 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 252 (accept_3_4 25 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 252 2 12 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 252 (Polychromatic418967fa.accept_16_7_2_12_1_1754 23 194 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 252 2 11 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 252
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 252 2 10 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 252 (accept_3_4 19 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 252 2 9 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 194 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 252 2 8 97 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 252 2 7 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 252 (accept_3_4 13 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 252 2 6 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 194 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 252 2 5 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 252
  (Polychromatic418967fa.accept_15_9_14_12_1_913 9 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 252 2 4 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 252 (accept_3_4 7 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  252 2 3 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 252 (Polychromatic418967fa.accept_23_5_10_22_1_15244 5 194 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 252 2 2 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 194 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 252 2 1 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 252 (accept_3_4 1 194 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 193 252 (Eq.refl Bool.true) (allA_succ_of_accept 59 193 252 (accept_3_5 59 193 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 193 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 58 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 193 252
  (Polychromatic418967fa.accept_25_7_18_2_1_15389 57 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 193 252 (accept_3_5 56 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 193 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 193 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 252 (Polychromatic418967fa.accept_17_3_6_14_1_4312 54 193
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 193 252 (accept_3_5 53 193
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 193 252
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 52 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 193 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 193 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 252 (accept_3_5 50 193 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 193 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 48 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 252 (accept_3_5 47 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 46 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 193 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 252 (accept_3_5 44 193 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 252 (Polychromatic418967fa.accept_16_11_1_12_1_1795 43 193 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 252
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 42 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 252 (accept_3_5 41 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 252 (Polychromatic418967fa.accept_15_10_13_12_1_3384 40 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 193 252 (Polychromatic418967fa.accept_19_1_3_5_1_3092 39 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 252 (accept_3_5 38 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 193 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 252
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 252 (accept_3_5 35 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 252 (Polychromatic418967fa.accept_16_2_1_12_1_3798 34 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 252 (accept_3_5 32 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 193
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 252
  (Polychromatic418967fa.accept_20_10_13_12_1_9726 30 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 193 252 (accept_3_5 29 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 193 252 (Polychromatic418967fa.accept_22_6_17_10_1_12202 28 193 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 193 252 (accept_3_5 26 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 193 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 252 (Polychromatic418967fa.accept_16_8_1_12_1_984 24 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 252 (accept_3_5 23 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 252 (Polychromatic418967fa.accept_25_22_18_2_1_15388 22
  193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 252 (accept_3_5 20 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 18 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 252 (accept_3_5 17 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 193
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 15 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 252 (accept_3_5 14 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 252 (Polychromatic418967fa.accept_23_12_9_22_1_15277 12 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 252 (accept_3_5 11 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 252 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10
  193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 252
  (Polychromatic418967fa.accept_25_9_18_2_1_15309 9 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 252 (accept_3_5 8 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 193 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 252 (accept_3_5 5 193 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 252 (Polychromatic418967fa.accept_16_4_1_12_1_1792 4 193 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 252
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 252 (accept_3_5 2 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 193 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 192 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 192 252 12 5 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 192 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 59 192
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 192 252 2 29 96 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 192 252 3 19 64 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 192 252 4 14 48
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 192 252
  (Polychromatic418967fa.accept_19_17_2_5_1_7085 55 192 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 192 252 6 9 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 192 252 (Polychromatic418967fa.accept_17_2_5_14_1_2068 53 192 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 192 252 4 13 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 192 252 3 17 64 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 192 252 2 25 96 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 192 252
  (Polychromatic418967fa.accept_22_5_16_10_1_7349 49 192 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 192 252 12 4 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 192 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 47 192 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 252 2 23 96 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 192 252 3 15 64 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 192 252 4 11 48 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 192 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 43 192 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 252 6 7 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 192 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 41 192 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 252 4 10 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 192 252 3 13 64 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 192 252 2 19 96 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 192 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 37 192 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 252 12 3 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 252 (Polychromatic418967fa.accept_19_16_2_5_1_5681 35 192 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 252 2 17 96 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 192 252 3 11 64 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 192 252 4 8 48 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 252
  (Polychromatic418967fa.accept_26_5_10_18_1_15387 31 192 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 192 252 6 5 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 192 252 (Polychromatic418967fa.accept_19_10_2_5_1_3059 29 192 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 252 4 7 48 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 192 252 3 9 64 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 192 252 2 13 96 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 252
  (Polychromatic418967fa.accept_22_3_16_10_1_7310 25 192 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 192 252 12 2 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 192 252 (Polychromatic418967fa.accept_19_4_2_5_1_5677 23 192 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 252 2 11 96 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 192 252 3 7 64 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 192 252 4 5 48 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 192 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 252 6 3 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 192 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 192 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 252 4 4 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 192 252 3 5 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 192 252 2 7 96 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 252
  (Polychromatic418967fa.accept_23_13_8_22_1_15208 13 192 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 192 252 12 1 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 192 252 (Polychromatic418967fa.accept_23_11_8_22_1_8821 11 192 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 252 2 5 96 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 192 252 3 3 64 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 192 252 4 2 48 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 252
  (Polychromatic418967fa.accept_19_7_2_5_1_5680 7 192 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 192 252 6 1 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 192 252 (Polychromatic418967fa.accept_22_5_16_10_1_7349 5 192 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 252 4 1 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 192 252 3 1 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 192 252 2 1 96 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 252 (Polychromatic418967fa.accept_23_1_8_22_1_15386 1 192
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 191 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 191 252 (accept_3_4 61 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 191 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 191 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 191 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 191 252 (accept_3_4 58 191 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 191 252 (Polychromatic418967fa.accept_23_11_7_22_1_15385 57 191 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 191 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 191 252 (accept_3_4 55 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 191 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 54 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 191 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 53 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 191 252 (accept_3_4 52 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 191 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 191 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 252
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 50 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 191 252 (accept_3_4 49 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 191 252 (Polychromatic418967fa.accept_22_4_15_10_1_13730 48 191 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 191 252
  (Polychromatic418967fa.accept_17_13_4_14_1_4272 47 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 191 252 (accept_3_4 46 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 191 252 (Polychromatic418967fa.accept_16_13_15_12_1_1748 45 191 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 252
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 44 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 191 252 (accept_3_4 43 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 191 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 42 191 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 41 191
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 252 (accept_3_4 40 191
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 39 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 191 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 38 191 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 252 (accept_3_4 37 191 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 191 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 252 (accept_3_4 34 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 252 (Polychromatic418967fa.accept_24_8_23_12_1_15313 32 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 252 (accept_3_4 31 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 30 191
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 29 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 252 (accept_3_4 28 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 252 (accept_3_4 25 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 191
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 252 (accept_3_4 22 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 252 (Polychromatic418967fa.accept_20_1_11_12_1_2467 21 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 252 (Polychromatic418967fa.accept_16_4_15_12_1_1745 20 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 252 (accept_3_4 19 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 191
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 252
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 252 (accept_3_4 16 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 252 (accept_3_4 13 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 252 (Polychromatic418967fa.accept_19_12_1_5_1_9924 12 191
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 252 (accept_3_4 10 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 252 (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 252 (accept_3_4 7 191 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 191 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 252 (accept_3_4 4 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 191 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 2 191 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 252 (accept_3_4 1 191 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  190 252 (Eq.refl Bool.true) (allA_succ_of_gcd 62 190 252 2 31 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 190 252 (Polychromatic418967fa.accept_25_11_15_2_1_15371 61 190
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 190 252 2 30 95 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 190 252 (accept_3_5 59
  190 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 190 252 2 29 95 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 190 252
  (Polychromatic418967fa.accept_17_6_3_14_1_2078 57 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 190 252 2 28 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 190 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 55 190 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 190 252 2 27 95 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 190 252 (accept_3_5 53 190 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 190 252 2 26 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 190 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  51 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 190 252 2 25 95 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 190 252
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 190 252 2 24 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 190 252 (accept_3_5 47 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 190 252 2 23 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 190 252 (Polychromatic418967fa.accept_17_11_3_14_1_6736 45 190 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 190 252 2 22 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 190 252
  (Polychromatic418967fa.accept_15_13_10_12_1_2503 43 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 190 252 2 21 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 190 252 (accept_3_5 41 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 190 252 2 20 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 190 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 190 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 190 252 2 19 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 190 252
  (Polychromatic418967fa.accept_15_7_10_12_1_2403 37 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 190 252 2 18 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 190 252 (accept_3_5 35 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 190 252 2 17 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 190 252 (Polychromatic418967fa.accept_20_13_10_12_1_2462 33 190 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 190 252 2 16 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 190 252
  (Polychromatic418967fa.accept_25_6_15_2_1_4439 31 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 190 252 2 15 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 190 252 (accept_3_5 29 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 190 252 2 14 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 190 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 190 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 252 2 13 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 190 252
  (Polychromatic418967fa.accept_13_12_8_5_1_976 25 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 190 252 2 12 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 190 252 (accept_3_5 23 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 252 2 11 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 190 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 252 2 10 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 252
  (Polychromatic418967fa.accept_17_2_3_14_1_8043 19 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 252 2 9 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 252 (accept_3_5 17 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 252 2 8 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 190 252 (Polychromatic418967fa.accept_17_15_3_14_1_4230 15 190 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 190 252 2 7 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 252
  (Polychromatic418967fa.accept_15_13_10_12_1_2503 13 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 190 252 2 6 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 190 252 (accept_3_5 11 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 252 2 5 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 190 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 252 2 4 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 252 2 3 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 252 (accept_3_5 5 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  252 2 2 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 3 190 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 252 2 1 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 190 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 189 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 189 252 63 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 189 252 (Polychromatic418967fa.accept_20_2_9_12_1_2546 62 189 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 189 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 61 189 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 189 252 3 20 63 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 189 252
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 189 252 (Polychromatic418967fa.accept_16_10_13_12_1_4873 58 189 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 189 252 3 19 63 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 189 252 7 8 27 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 189 252
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 189 252 9 6 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 189 252 (Polychromatic418967fa.accept_22_9_13_10_1_15214 53 189 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 252
  (Polychromatic418967fa.accept_16_4_13_12_1_1740 52 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 189 252 3 17 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 189 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 50 189 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 189 252 7 7 27 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 189 252 3 16 63 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 189 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 252 (Polychromatic418967fa.accept_22_2_13_10_1_13758 46 189 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 189 252 9 5 21 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 189 252
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 44 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 189 252 (Polychromatic418967fa.accept_20_3_9_12_1_6671 43 189 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 189 252 21 2 9 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 189 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 252 (Polychromatic418967fa.accept_15_10_9_12_1_2497 40 189 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 189 252 3 13 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 189 252
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 38 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 189 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 189 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 189 252 9 4 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 189 252 7 5 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 189 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  34 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 189 252 3 11 63 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 189 252
  (Polychromatic418967fa.accept_19_13_18_5_1_8619 32 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 189 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 189 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 189 252 3 10 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 189 252
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 189 252 7 4 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 27 189 252 9 3 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 189 252 (Polychromatic418967fa.accept_16_10_13_12_1_4873 26 189 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 25 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 189 252 3 8 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 189 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 189 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 252 (Polychromatic418967fa.accept_17_5_2_14_1_4270 22 189
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 189 252 21 1 9 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 189 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 189 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 189 252 9 2 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 189 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 17
  189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 252
  (Polychromatic418967fa.accept_17_16_2_14_1_6715 16 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 189 252 3 5 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 189 252 7 2 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 189 252 (Polychromatic418967fa.accept_19_13_18_5_1_8619 13 189 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 189 252 3 4 63 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 189 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 252 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 189 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 252 9 1 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 252 (Polychromatic418967fa.accept_16_8_13_12_1_3809
  8 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 189 252 7 1 27 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 189 252 3 2 63 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 189 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 252 3 1 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 189 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 189 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 189 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 188 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 188 252 4 16 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 188 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 188 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 188 252 2 31 94 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 188 252 (accept_3_4 61 188 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 188 252 4 15 47 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 188 252
  (Polychromatic418967fa.accept_19_2_17_5_1_5643 59 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 188 252 2 29 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 188 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 57 188 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 188 252 4 14 47 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 188 252 (accept_3_4 55 188 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 188 252 2 27 94 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 188 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 53 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 188 252 4 13 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 188 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 188 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 188 252 2 25 94 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 188 252 (accept_3_4 49 188 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 188 252 4 12 47 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 188 252
  (Polychromatic418967fa.accept_17_13_1_14_1_1149 47 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 188 252 2 23 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 188 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 188 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 188 252 4 11 47 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 188 252 (accept_3_4 43 188 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 188 252 2 21 94 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 188 252
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 41 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 188 252 4 10 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 188 252 (Polychromatic418967fa.accept_25_14_13_2_1_15384 39 188 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 188 252 2 19 94 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 188 252 (accept_3_4 37
  188 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 188 252 4 9 47 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 188 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 35 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 188 252 2 17 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 188 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 188 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 188 252 4 8 47 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 188 252 (accept_3_4 31 188 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 188 252 2 15 94 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 188 252
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 188 252 4 7 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 188 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 188 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 188 252 2 13 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 188 252 (accept_3_4 25 188 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 188 252 4 6 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 188 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 188
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 252 2 11 94 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 252
  (Polychromatic418967fa.accept_17_4_1_14_1_4296 21 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 252 4 5 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 188 252 (accept_3_4 19 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  188 252 2 9 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 188 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 188 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 252 4 4 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 252 (Polychromatic418967fa.accept_10_5_8_2_1_517
  15 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 252 2 7 94 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 252
  (accept_3_4 13 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 252 4 3 47 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 252
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 188 252 2 5 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 188 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 188 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 188 252 4 2 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 188 252 (accept_3_4 7 188 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188 252 2 3 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 188 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 188 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 188 252 4 1 47 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 188 252
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 188 252 2 1 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 188 252 (accept_3_4 1 188 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 187 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 187 252 (accept_3_5 65 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 187 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 187 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 187 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 187 252 (accept_3_5 62 187 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 187 252 (Polychromatic418967fa.accept_27_7_25_9_1_3618 61 187 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 187 252
  (Polychromatic418967fa.accept_19_3_16_5_1_7098 60 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 187 252 (accept_3_5 59 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 187 252 (Polychromatic418967fa.accept_16_10_11_12_1_4835 58 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 187 252 (Polychromatic418967fa.accept_20_17_7_12_1_6632 57 187 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 187 252 (accept_3_5 56 187 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 187 252 (Polychromatic418967fa.accept_8_7_3_4_1_404
  55 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 187 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 187 252 (accept_3_5 53 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 187 252 (Polychromatic418967fa.accept_16_4_11_12_1_1775 52 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 187 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 51 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 252 (accept_3_5 50 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 187 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 187
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 187 252
  (Polychromatic418967fa.accept_15_3_7_12_1_372 48 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 187 252 (accept_3_5 47 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 187 252 (Polychromatic418967fa.accept_19_8_16_5_1_8583 46 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 187 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 252 (accept_3_5 44 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 187 252 (Polychromatic418967fa.accept_22_21_11_10_1_12218 43
  187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 187 252
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 42 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 187 252 (accept_3_5 41 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 187 252 (Polychromatic418967fa.accept_15_10_7_12_1_2490 40 187 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 252 (Polychromatic418967fa.accept_8_7_3_4_1_404
  39 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 252 (accept_3_5 38
  187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 187 252
  (Polychromatic418967fa.accept_20_17_7_12_1_6632 37 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 187 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 36 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 252 (accept_3_5 35 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 187
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 252
  (Polychromatic418967fa.accept_15_3_7_12_1_372 33 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 187 252 (accept_3_5 32 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 187 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 187 252 (Polychromatic418967fa.accept_19_11_16_5_1_5667 30 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 252 (accept_3_5 29 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 252 (Polychromatic418967fa.accept_24_4_19_12_1_10276 28
  187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 252
  (Polychromatic418967fa.accept_19_8_16_5_1_8583 27 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 187 252 (accept_3_5 26 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 252 (accept_3_5 23 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 252 (Polychromatic418967fa.accept_19_3_16_5_1_7098 22 187
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 252
  (Polychromatic418967fa.accept_15_6_7_12_1_869 21 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 252 (accept_3_5 20 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 18 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 252 (accept_3_5 17 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 252 (Polychromatic418967fa.accept_24_16_19_12_1_8458 16
  187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 252 (accept_3_5 14 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 252 (Polychromatic418967fa.accept_23_13_3_22_1_3745 13 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 252 (Polychromatic418967fa.accept_19_12_16_5_1_12620 12 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 252 (accept_3_5 11 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 252 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 187
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 9 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 252 (accept_3_5 8 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 6 187 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 252 (accept_3_5 5 187 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 187 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 252
  (Polychromatic418967fa.accept_15_3_7_12_1_372 3 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 252 (accept_3_5 2 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 252 (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 187 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 186 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 66 186 252 6 11 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 186 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 65 186
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 186 252 2 32 93 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 186 252 3 21 62 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 186 252 2 31 93
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 186 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 61 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 252 6 10 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 252 (Polychromatic418967fa.accept_16_11_10_12_1_4832 59 186 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 186 252 2 29 93 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 186 252 3 19 62 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 186 252 2 28 93 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 186 252
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 55 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 186 252 6 9 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 186 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 53 186 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 186 252 2 26 93 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 186 252 3 17 62 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 186 252 2 25 93 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 186 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 49 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 252 6 8 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 186 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 47 186 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 252 2 23 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 186 252 3 15 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 186 252 2 22 93 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 252
  (Polychromatic418967fa.accept_16_11_10_12_1_4832 43 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 186 252 6 7 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 186 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 186 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 252 2 20 93 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 186 252 3 13 62 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 186 252 2 19 93 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 252 6 6 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 186 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 35 186 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 252 2 17 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 186 252 3 11 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 186 252 2 16 93 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 252 6 5 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 186 252 (Polychromatic418967fa.accept_16_13_10_12_1_1811 29 186 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 252 2 14 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 186 252 3 9 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 186 252 2 13 93 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 252
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 252 6 4 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 186 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 186 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 252 2 11 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 186 252 3 7 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 186 252 2 10 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 252 6 3 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 186 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 186 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 252 2 8 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 186 252 3 5 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 186 252 2 7 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 252
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 186 252 6 2 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 186 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 186 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 252 2 5 93 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 186 252 3 3 62 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 186 252 2 4 93 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 252 6 1 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 186 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186 252 2 2 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 186 252 3 1 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 186 252 2 1 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  186 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 185 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 185 252 (accept_3_4 67 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 185 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 66 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 185 252 (Polychromatic418967fa.accept_19_8_14_5_1_9919 65 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 185 252 (accept_3_4 64 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 185 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 185 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 185 252
  (Polychromatic418967fa.accept_15_2_5_12_1_369 62 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 185 252 (accept_3_4 61 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 185 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 60 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 185 252 (Polychromatic418967fa.accept_19_2_14_5_1_5715 59 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 185 252 (accept_3_4 58 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 185 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 185
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 185 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 56 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 185 252 (accept_3_4 55 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 185 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 185 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 185 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 185 252 (accept_3_4 52 185 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 185 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 185 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 185 252
  (Polychromatic418967fa.accept_13_11_3_5_1_982 50 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 185 252 (accept_3_4 49 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 185 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 185 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 47 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 252 (accept_3_4 46 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 185 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 185 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 252
  (Polychromatic418967fa.accept_19_6_14_5_1_4339 44 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 185 252 (accept_3_4 43 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 252 (Polychromatic418967fa.accept_24_18_17_12_1_3252 42 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 252 (accept_3_4 40 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 185
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 252 (accept_3_4 37 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 185 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 252 (accept_3_4 34 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 185 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 252
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 32 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 252 (accept_3_4 31 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 185 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 252 (accept_3_4 28 185 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 252
  (Polychromatic418967fa.accept_20_6_5_12_1_8169 26 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 252 (accept_3_4 25 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 185 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 252 (accept_3_4 22 185 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 252
  (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 252 (accept_3_4 19 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 252 (accept_3_4 16 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 185
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 252 (accept_3_4 13 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 252 (accept_3_4 10 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 185 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 252 (accept_3_4 7 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 252 (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 185 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 252 (accept_3_4 4 185 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 185 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 252
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 252 (accept_3_4 1 185 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 184 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 184 252 4 17 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 184 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 67 184 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 184 252 2 33 92 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 184 252 (accept_3_5 65 184 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 184 252 4 16 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 184 252
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 184 252 2 31 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 184 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 61 184 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 184 252 4 15 46 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 184 252 (accept_3_5 59 184 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 184 252 2 29 92 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 184 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 184 252 4 14 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 184 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 55 184 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 184 252 2 27 92 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 184 252 (accept_3_5 53 184 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 184 252 4 13 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 184 252
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 51 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 184 252 2 25 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 184 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 49 184 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 184 252 4 12 46 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 184 252 (accept_3_5 47 184 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 184 252 2 23 92 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 184 252
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 184 252 4 11 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 184 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 43 184 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 184 252 2 21 92 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 184 252 (accept_3_5 41 184 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 184 252 4 10 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 184 252
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 184 252 2 19 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 184 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 184 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 184 252 4 9 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 184 252 (accept_3_5 35 184 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 184 252 2 17 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 184 252 (Polychromatic418967fa.accept_13_7_2_5_1_2344
  33 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 184 252 4 8 46 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 184 252
  (Polychromatic418967fa.accept_11_9_8_10_1_934 31 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 184 252 2 15 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 184 252 (accept_3_5 29 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 184 252 4 7 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 184 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 184 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 252 2 13 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634
  25 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 184 252 4 6 46 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 184 252
  (accept_3_5 23 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 184 252 2 11 92 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 184 252
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 184 252 4 5 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 184 252 (Polychromatic418967fa.accept_16_3_8_12_1_2736 19 184 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 184 252 2 9 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 184 252 (accept_3_5 17 184 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 184 252 4 4 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 184 252 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 184
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 252 2 7 92 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 252
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 13 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 184 252 4 3 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 184 252 (accept_3_5 11 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 184 252 2 5 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 184 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 184 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 252 4 2 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 7
  184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 252 2 3 92 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 252 (accept_3_5 5
  184 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 252 4 1 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 184 252
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 184 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 184 252 2 1 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 184 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1 184 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 184 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 183 252 (Eq.refl Bool.true) (allA_succ_of_gcd 69 183 252 3 23 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 183 252
  (Polychromatic418967fa.accept_13_3_1_5_1_499 68 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 183 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 183 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 183 252 3 22 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 183 252 (Polychromatic418967fa.accept_10_5_3_2_1_899
  65 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 64 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 183 252 3 21 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 183 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 62 183 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 183 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 61 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 183 252 3 20 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 183 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 183 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 252 (Polychromatic418967fa.accept_11_3_7_10_1_180
  58 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 183 252 3 19 61 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 183 252
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 56 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 183 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 183 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 183 252 3 18 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 183 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657
  53 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 52 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 183 252 3 17 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 183 252 (Polychromatic418967fa.accept_16_2_7_12_1_3793 50 183 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 252
  (Polychromatic418967fa.accept_19_11_12_5_1_7124 49 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 183 252 3 16 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 183 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 47 183 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 252
  (Polychromatic418967fa.accept_19_8_12_5_1_7122 46 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 183 252 3 15 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 183 252 (Polychromatic418967fa.accept_17_10_13_14_1_3094 44 183 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 183 252 3 14 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 183 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 41 183 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 252
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 40 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 183 252 3 13 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 183 252 (Polychromatic418967fa.accept_13_12_1_5_1_1650 38 183 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 37 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 183 252 3 12 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 183 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 183 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176
  34 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 183 252 3 11 61 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 183 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 32 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 183 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 183 252 3 10 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 183 252 (Polychromatic418967fa.accept_13_3_1_5_1_499
  29 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 183 252 3 9 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 183 252 (Polychromatic418967fa.accept_19_7_12_5_1_7123 26 183 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 25 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 183 252 3 8 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 183 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 183 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 22 183
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 252 3 7 61 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 252
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 183 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 183 252 3 6 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 183 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628
  17 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 252
  (Polychromatic418967fa.accept_13_3_1_5_1_499 16 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 183 252 3 5 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 183 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 183 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 252 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 183
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 252 3 4 61 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 252 (Polychromatic418967fa.accept_17_10_13_14_1_3094 10 183 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 252 3 3 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176 8
  183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 183 252 3 2 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 183 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 183 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 183 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 252 3 1 61 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 252
  (Polychromatic418967fa.accept_15_2_3_12_1_891 2 183 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 183 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 182 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 182 252 14 5 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 182 252 (Polychromatic418967fa.accept_19_12_11_5_1_950 69 182 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 182 252 2 34 91 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 182 252 (accept_3_4 67 182 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 182 252 2 33 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 182 252
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 65 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 182 252 2 32 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 182 252 7 9 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 182 252 2 31 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 182 252 (accept_3_4 61 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 182 252 2 30 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 182 252 (Polychromatic418967fa.accept_15_14_2_12_1_2472 59 182 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 182 252 2 29 91 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 182 252
  (Polychromatic418967fa.accept_20_17_2_12_1_8168 57 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 182 252 14 4 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 182 252 (accept_3_4 55 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 182 252 2 27 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 182 252 (Polychromatic418967fa.accept_19_15_11_5_1_5713 53 182 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 252 2 26 91 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 252
  (Polychromatic418967fa.accept_15_6_2_12_1_885 51 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 182 252 2 25 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 182 252 7 7 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 182 252 2 24 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 182 252 (Polychromatic418967fa.accept_20_7_2_12_1_6642 47 182 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 252 2 23 91 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 252
  (Polychromatic418967fa.accept_17_11_12_14_1_5431 45 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 182 252 2 22 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 182 252 (accept_3_4 43 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 252 14 3 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 252 (Polychromatic418967fa.accept_27_14_20_9_1_15383 41 182 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 252 2 20 91 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 252
  (Polychromatic418967fa.accept_20_19_2_12_1_2516 39 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 182 252 2 19 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 182 252 (accept_3_4 37 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 252 2 18 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 182 252 7 5 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 182 252 2 17 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 182 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 33 182 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 182 252 2 16 91 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 182 252 (accept_3_4 31 182 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 182 252 2 15 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 182 252
  (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 182 252 14 2 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 182 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 182 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 182 252 2 13 91 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 182 252 (accept_3_4 25 182 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 182 252 2 12 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 182 252
  (Polychromatic418967fa.accept_25_23_7_2_1_15289 23 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 182 252 2 11 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 182 252 7 3 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 182 252 2 10 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 182 252 (accept_3_4 19 182 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 182 252 2 9 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 182 252 (Polychromatic418967fa.accept_19_17_11_5_1_7092 17 182 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 252 2 8 91 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 252
  (Polychromatic418967fa.accept_17_15_12_14_1_2087 15 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 182 252 14 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 182 252 (accept_3_4 13 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 252 2 6 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 252 (Polychromatic418967fa.accept_17_11_12_14_1_5431 11 182 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 252 2 5 91 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 252
  (Polychromatic418967fa.accept_17_9_12_14_1_5423 9 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 252 2 4 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 182 252 7 1 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 182 252 2 3 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 182 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 182 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 182 252 2 2 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 182 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469
  3 182 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 252 2 1 91 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 252 (accept_3_4 1
  182 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 181 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 181 252 (accept_3_5 71 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 181 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 70 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 181 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 69 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 181 252 (accept_3_5 68 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 181 252 (Polychromatic418967fa.accept_13_2_12_5_1_1602 67 181
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 181 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 66 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 181 252 (accept_3_5 65 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 181 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 64 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 181 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 181 252 (accept_3_5 62 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 181 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 61 181
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 181 252
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 60 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 181 252 (accept_3_5 59 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 181 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 58 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 181 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 181 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 181 252 (accept_3_5 56 181 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 181 252 (Polychromatic418967fa.accept_16_7_5_12_1_4824 55 181 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 181 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 54 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 181 252 (accept_3_5 53 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 181 252 (Polychromatic418967fa.accept_16_4_5_12_1_2749 52 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 181 252 (Polychromatic418967fa.accept_19_13_10_5_1_11329 51 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 181 252 (accept_3_5 50 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 181 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 181 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 181 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 48 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 181 252 (accept_3_5 47 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 181 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 181 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 181 252 (accept_3_5 44 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 181 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 181
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 181 252
  (Polychromatic418967fa.accept_16_10_5_12_1_4925 42 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 181 252 (accept_3_5 41 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 181 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 40 181 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 181
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 252 (accept_3_5 38 181
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 181 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 37 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 181 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 181 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 252 (accept_3_5 35 181 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 181 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 34 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 252 (accept_3_5 32 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 252 (Polychromatic418967fa.accept_20_11_1_12_1_3803 31 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 252 (accept_3_5 29 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 28 181
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 252
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 252 (accept_3_5 26 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 252 (Polychromatic418967fa.accept_16_8_5_12_1_3812 24 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 252 (accept_3_5 23 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 252 (Polychromatic418967fa.accept_19_3_10_5_1_4314 22 181
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 252
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 252 (accept_3_5 20 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 252 (Polychromatic418967fa.accept_19_18_10_5_1_12639 18 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 252 (accept_3_5 17 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 181
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 252 (accept_3_5 14 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 252 (Polychromatic418967fa.accept_17_12_11_14_1_3120 12 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 252 (accept_3_5 11 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 252 (Polychromatic418967fa.accept_16_10_5_12_1_4925 10 181
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 252 (accept_3_5 8 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 181 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 252 (accept_3_5 5 181 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 181 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 3 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 252 (accept_3_5 2 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 181 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73
  180 252 (Eq.refl Bool.true) (allA_succ_of_gcd 72 180 252 36 2 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 180 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 71 180
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 180 252 2 35 90 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 180 252 3 23 60 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 180 252 4 17 45
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 180 252
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 67 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 252 6 11 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 180 252 (Polychromatic418967fa.accept_16_1_4_12_1_376 65 180 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 180 252 4 16 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 180 252 9 7 20 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 180 252 2 31 90 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 180 252
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 61 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 180 252 12 5 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 180 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 59 180 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 252 2 29 90 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 180 252 3 19 60 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 180 252 4 14 45 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 180 252
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 55 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 180 252 18 3 10 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 180 252 (Polychromatic418967fa.accept_16_5_4_12_1_3800 53 180 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 252 4 13 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 180 252 3 17 60 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 180 252 2 25 90 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 49 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 252 12 4 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 252 (Polychromatic418967fa.accept_16_15_4_12_1_2731 47 180 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 252 2 23 90 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 180 252 9 5 20 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 252 4 11 45 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 252
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 43 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 180 252 6 7 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 180 252 (Polychromatic418967fa.accept_16_9_4_12_1_4896 41 180 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 252 4 10 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 180 252 3 13 60 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 180 252 2 19 90 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 252
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 37 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 252 36 1 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 180 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 35 180 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 252 2 17 90 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 180 252 3 11 60 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 180 252 4 8 45 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 252
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 31 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 180 252 6 5 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 180 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 180 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 252 4 7 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 180 252 9 3 20 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 180 252 2 13 90 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 252
  (Polychromatic418967fa.accept_16_9_4_12_1_4896 25 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 252 12 2 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 180 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 252 2 11 90 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 252 3 7 60 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 180 252 4 5 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 252
  (Polychromatic418967fa.accept_13_6_11_5_1_133 19 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 252 18 1 10 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 252 (Polychromatic418967fa.accept_16_1_4_12_1_376 17 180 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 252 4 4 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 252 3 5 60 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 252 2 7 90 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 252
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 180 252 12 1 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 180 252 (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 180 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 252 2 5 90 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 252 9 1 20 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 252 4 2 45 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 252
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 180 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 252 6 1 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 180 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 252 4 1 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 252 3 1 60 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 252 2 1 90 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 252 (Polychromatic418967fa.accept_16_1_4_12_1_376 1 180 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 179 252 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 179 252 (accept_3_4 73 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 179 252 (Polychromatic418967fa.accept_16_8_3_12_1_1819 72 179 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 179 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 179 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 179 252 (accept_3_4 70 179 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 179 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 69 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 179 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 68 179 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 179 252 (accept_3_4 67 179 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 179 252 (Polychromatic418967fa.accept_24_18_11_12_1_10310 66 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 179 252
  (Polychromatic418967fa.accept_22_21_3_10_1_5763 65 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 179 252 (accept_3_4 64 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 179 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 179 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 179 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 62 179
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 179 252 (accept_3_4 61 179
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 179 252
  (Polychromatic418967fa.accept_13_8_10_5_1_977 60 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 179 252 (Polychromatic418967fa.accept_19_2_8_5_1_1885 59 179 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 179 252 (accept_3_4 58 179 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 179 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 56 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 179 252 (accept_3_4 55 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 179 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 54 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 252 (Polychromatic418967fa.accept_20_13_19_12_1_5143 53 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 252 (accept_3_4 52 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 179 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 252
  (Polychromatic418967fa.accept_19_12_8_5_1_8538 50 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 179 252 (accept_3_4 49 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 179 252 (Polychromatic418967fa.accept_19_10_8_5_1_5689 48 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 179 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 179 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 252 (accept_3_4 46 179 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 252 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 179 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 252
  (Polychromatic418967fa.accept_24_20_11_12_1_15217 44 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 179 252 (accept_3_4 43 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 179 252 (Polychromatic418967fa.accept_16_10_3_12_1_1758 42 179 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 252 (Polychromatic418967fa.accept_10_1_9_2_1_45
  41 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 252 (accept_3_4 40
  179 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 179 252 (Polychromatic418967fa.accept_17_4_9_14_1_5406 38 179 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 252 (accept_3_4 37 179 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 179 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 36 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 252
  (Polychromatic418967fa.accept_19_16_8_5_1_4322 35 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 179 252 (accept_3_4 34 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 179 252 (Polychromatic418967fa.accept_19_14_8_5_1_8606 33 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 179 252 (Polychromatic418967fa.accept_13_6_10_5_1_1648 32 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 252 (accept_3_4 31 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 30 179
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 252 (accept_3_4 28 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 252 (accept_3_4 25 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 179
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 252 (accept_3_4 22 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 20 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 252 (accept_3_4 19 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 179
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 252 (accept_3_4 16 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 252 (Polychromatic418967fa.accept_19_14_8_5_1_8606 14 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 252 (accept_3_4 13 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 252 (Polychromatic418967fa.accept_17_12_9_14_1_4283 12 179
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 252 (accept_3_4 10 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 8 179 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 252 (accept_3_4 7 179 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 252 (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 252
  (Polychromatic418967fa.accept_17_5_9_14_1_4282 5 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 252 (accept_3_4 4 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 252 (Polychromatic418967fa.accept_19_3_8_5_1_1875 3 179 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 2 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 252 (accept_3_4 1 179 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 179
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 178 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 178 252 2 37 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 178 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800 73 178 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 178 252 2 36 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 178 252 (accept_3_5 71 178 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 178 252 2 35 89 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 178 252
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 69 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 178 252 2 34 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 178 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 67 178 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 178 252 2 33 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 178 252 (accept_3_5 65 178 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 178 252 2 32 89 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 178 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 63 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 178 252 2 31 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 178 252 (Polychromatic418967fa.accept_15_1_13_12_1_347 61 178 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 178 252 2 30 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 178 252 (accept_3_5 59 178 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 178 252 2 29 89 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 178 252
  (Polychromatic418967fa.accept_16_9_2_12_1_1800 57 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 178 252 2 28 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 178 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 55 178 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 178 252 2 27 89 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 178 252 (accept_3_5 53 178 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 178 252 2 26 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 178 252 (Polychromatic418967fa.accept_19_13_7_5_1_5712
  51 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 252 2 25 89 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 252
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 49 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 178 252 2 24 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 178 252 (accept_3_5 47 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 252 2 23 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 178 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 252 2 22 89 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 252
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 43 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 252 2 21 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 252 (accept_3_5 41 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 252 2 20 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 252 (Polychromatic418967fa.accept_16_7_2_12_1_1754 39 178 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 252 2 19 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 252
  (Polychromatic418967fa.accept_31_6_23_4_1_15382 37 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 178 252 2 18 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 178 252 (accept_3_5 35 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 252 2 17 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 33 178 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 252 2 16 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 252
  (Polychromatic418967fa.accept_15_1_13_12_1_347 31 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 252 2 15 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 252 (accept_3_5 29 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 252 2 14 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 178 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 252 2 13 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 252 2 12 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 252 (accept_3_5 23 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 252 2 11 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 252 (Polychromatic418967fa.accept_19_2_7_5_1_3067 21 178 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 252 2 10 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 252
  (Polychromatic418967fa.accept_25_19_3_2_1_4454 19 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 252 2 9 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 252 (accept_3_5 17 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 252 2 8 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 178 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 252 2 7 89 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 252
  (Polychromatic418967fa.accept_19_13_7_5_1_5712 13 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 252 2 6 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 252 (accept_3_5 11 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 252 2 5 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 178 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 252 2 4 89 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 252
  (Polychromatic418967fa.accept_16_7_2_12_1_1754 7 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 252 2 3 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 252 (accept_3_5 5 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  252 2 2 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 178 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 252 2 1 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 178 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 177 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 177 252 3 25 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 177 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 252
  (Polychromatic418967fa.accept_27_19_15_9_1_15381 73 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 177 252 3 24 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 177 252 (Polychromatic418967fa.accept_19_14_6_5_1_9917 71 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 177 252
  (Polychromatic418967fa.accept_23_1_16_22_1_3788 70 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 177 252 3 23 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 177 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 68 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 177 252
  (Polychromatic418967fa.accept_20_7_17_12_1_11156 67 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 177 252 3 22 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 177 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 65 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 64 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 177 252 3 21 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 177 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 62 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 61 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 177 252 3 20 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 177 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 59 177 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 252 (Polychromatic418967fa.accept_19_1_6_5_1_4319
  58 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 177 252 3 19 59 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 177 252
  (Polychromatic418967fa.accept_16_8_1_12_1_984 56 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 177 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 177 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 177 252 3 18 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 177 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 53
  177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 252
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 52 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 177 252 3 17 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 177 252 (Polychromatic418967fa.accept_16_2_1_12_1_3798 50 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 49 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 177 252 3 16 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 177 252 (Polychromatic418967fa.accept_20_7_17_12_1_11156 47 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 46 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 177 252 3 15 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 177 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 177 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 252
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 43 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 177 252 3 14 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 177 252 (Polychromatic418967fa.accept_19_3_6_5_1_9947 41 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 252
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 40 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 177 252 3 13 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 177 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 38 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 37 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 177 252 3 12 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 177 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 177 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 252 (Polychromatic418967fa.accept_10_4_7_2_1_211
  34 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 177 252 3 11 59 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 177 252
  (Polychromatic418967fa.accept_27_5_15_9_1_13385 32 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 177 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 177 252 3 10 59 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 177 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 252 (Polychromatic418967fa.accept_27_1_15_9_1_13488 28 177 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 177 252 3 9 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 252
  (Polychromatic418967fa.accept_19_7_6_5_1_4320 26 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 177 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 252 3 8 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616
  23 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 252
  (Polychromatic418967fa.accept_19_3_6_5_1_9947 22 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 177 252 3 7 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 177 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 177 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 177
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 252 3 6 59 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 252
  (Polychromatic418967fa.accept_23_17_16_22_1_13680 17 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 177 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 16 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 252 3 5 59 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 177 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 252 3 4 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 252
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 177 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 177 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 252 3 3 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 252
  (Polychromatic418967fa.accept_16_8_1_12_1_984 8 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 252 (Polychromatic418967fa.accept_19_7_6_5_1_4320 7 177 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 252 3 2 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 177 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 177 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 177 252 3 1 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 177 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 2 177 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 177 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 176 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 176 252 4 19 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 176 252 (Polychromatic418967fa.accept_17_7_6_14_1_6737 75 176 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 176 252 2 37 88 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 176 252 (accept_3_4 73 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 176 252 4 18 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 176 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 71 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 176 252 2 35 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 176 252 (Polychromatic418967fa.accept_27_15_14_9_1_15380 69 176 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 176 252 4 17 44 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 176 252 (accept_3_4 67 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 176 252 2 33 88 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 176 252
  (Polychromatic418967fa.accept_23_19_15_22_1_8770 65 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 176 252 4 16 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 176 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 63 176 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 176 252 2 31 88 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 176 252 (accept_3_4 61 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 176 252 4 15 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 176 252
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 59 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 176 252 2 29 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 176 252 (Polychromatic418967fa.accept_23_11_15_22_1_5334 57 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 176 252 4 14 44 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 176 252 (accept_3_4 55
  176 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 176 252 2 27 88 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 176 252
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 53 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 176 252 4 13 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 176 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 176 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 176 252 2 25 88 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 176 252 (accept_3_4 49 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 176 252 4 12 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 176 252
  (Polychromatic418967fa.accept_23_1_15_22_1_15379 47 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 176 252 2 23 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 176 252 (Polychromatic418967fa.accept_25_20_1_2_1_15378 45 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 176 252 4 11 44 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 176 252 (accept_3_4 43
  176 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 176 252 2 21 88 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 176 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 176 252 4 10 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 176 252 (Polychromatic418967fa.accept_23_16_15_22_1_5332 39 176 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 176 252 2 19 88 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 176 252 (accept_3_4 37 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 176 252 4 9 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 176 252
  (Polychromatic418967fa.accept_24_11_8_12_1_10243 35 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 176 252 2 17 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 176 252 (Polychromatic418967fa.accept_26_7_20_18_1_15377 33 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 252 4 8 44 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 252 (accept_3_4 31
  176 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 252 2 15 88 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 252
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 29 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 176 252 4 7 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 176 252 (Polychromatic418967fa.accept_30_27_26_12_1_15376 27 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 252 2 13 88 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 252 (accept_3_4 25
  176 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 252 4 6 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 252
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 176 252 2 11 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 176 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 176 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 176 252 4 5 44 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 176 252 (accept_3_4 19 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 176 252 2 9 88 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 176 252
  (Polychromatic418967fa.accept_24_17_8_12_1_8499 17 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 176 252 4 4 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 176 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 176 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 252 2 7 88 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 252 (accept_3_4 13 176 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 252 4 3 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 176 252 2 5 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 176 252 (Polychromatic418967fa.accept_25_9_1_2_1_15237 9 176 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 252 4 2 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 252 (accept_3_4 7 176 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 252 2 3 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 252 (Polychromatic418967fa.accept_24_5_8_12_1_15245 5 176
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 252 4 1 44 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 252
  (Polychromatic418967fa.accept_17_3_6_14_1_4312 3 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 176 252 2 1 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 176 252 (accept_3_4 1 176 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 175 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 175 252 7 11 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 175 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 76 175 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 175 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 75 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 175 252 (accept_3_5 74 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 175 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 73 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 175 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 72 175 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 175 252 (accept_3_5 71 175 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 175 252 7 10 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 175 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333
  69 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 175 252 (accept_3_5 68
  175 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 175 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 67 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 175 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 66 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 175 252 (accept_3_5 65 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 175 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 64 175 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 175 252 7 9 25 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 175 252 (accept_3_5 62 175 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 175 252
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 61 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 175 252 (Polychromatic418967fa.accept_17_9_5_14_1_4277 60 175 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 175 252 (accept_3_5 59 175 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 175 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 58 175
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 57 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 175 252 7 8 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 175 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 55 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 175 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 54 175
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 252 (accept_3_5 53 175
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 175 252
  (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 175 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 175 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 175 252 (accept_3_5 50 175 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 49 175 252 7 7 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 175 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 175 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 252 (accept_3_5 47 175 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 252 (Polychromatic418967fa.accept_19_8_4_5_1_8569
  46 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 252
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 45 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 175 252 (accept_3_5 44 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 175 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 175 252 7 6 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 175 252 (accept_3_5 41 175 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 40 175 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 175 252 (accept_3_5 38 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 175 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 175
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 175 252 7 5 25 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 175 252
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 34 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 175 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 175 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 252 (accept_3_5 32 175 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 252 (Polychromatic418967fa.accept_19_12_4_5_1_9936 31 175 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 252
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 30 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 175 252 (accept_3_5 29 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  175 252 7 4 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 175 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 175 252 (accept_3_5 26 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 175 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 175
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 252 (accept_3_5 23 175
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 252
  (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 175 252 7 3 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 175 252 (accept_3_5 20 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 175 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 175
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 252 (accept_3_5 17 175
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 252
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 16 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 175 252 (Polychromatic418967fa.accept_19_15_4_5_1_11338 15 175 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 175 252 7 2 25 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 175 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 13 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 175 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 252 (accept_3_5 11 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 175 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 175 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 252 (accept_3_5 8 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 175
  252 7 1 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  175 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 175 252 (accept_3_5 5 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 175 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 175 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 175 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 252 (accept_3_5 2 175 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610
  1 175 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 174 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 174 252 6 13 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 174 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 174 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 174 252 2 38 87 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 174 252 3 25 58 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 174 252 2 37 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 174 252
  (Polychromatic418967fa.accept_19_16_3_5_1_5684 73 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 252 6 12 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 252 (Polychromatic418967fa.accept_19_14_3_5_1_11347 71 174 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 174 252 2 35 87 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 174 252 3 23 58 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 174 252 2 34 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 174 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 67 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 252 6 11 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 65 174 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 174 252 2 32 87 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 174 252 3 21 58 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 174 252 2 31 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 252
  (Polychromatic418967fa.accept_22_17_20_10_1_12161 61 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 174 252 6 10 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 174 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 174 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 252 2 29 87 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 174 252 3 19 58 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 174 252 2 28 87
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 252
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 174 252 6 9 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 174 252 (Polychromatic418967fa.accept_24_5_6_12_1_13633 53 174 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 252 2 26 87 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 174 252 3 17 58 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 174 252 2 25 87
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 252
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 49 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 252 6 8 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 174 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 174 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 252 2 23 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 174 252 3 15 58 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 174 252 2 22 87 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 252
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 43 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 252 6 7 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 174 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 174 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 252 2 20 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 174 252 3 13 58 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 174 252 2 19 87 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 252 6 6 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 174 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 35 174 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 252 2 17 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 174 252 3 11 58 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 174 252 2 16 87 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 252
  (Polychromatic418967fa.accept_23_8_13_22_1_13677 31 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 174 252 6 5 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 174 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 174 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 252 2 14 87 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 174 252 3 9 58 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 174 252 2 13 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 252
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 174 252 6 4 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 174 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 174 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 252 2 11 87 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 252 3 7 58 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 252 2 10 87 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 252
  (Polychromatic418967fa.accept_11_8_9_10_1_503 19 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 252 6 3 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 174 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 252 2 8 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 252 3 5 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 252 2 7 87 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 252
  (Polychromatic418967fa.accept_17_13_4_14_1_4272 13 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 174 252 6 2 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 174 252 (Polychromatic418967fa.accept_24_11_6_12_1_15281 11 174 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 252 2 5 87 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 174 252 3 3 58 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 252 2 4 87 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 252 6 1 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 174 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 252 2 2 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 174 252 3 1 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 174 252 2 1 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 1
  174 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 173 252 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 173 252 (accept_3_4 79 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 173 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 78 173 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 173 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 77 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 173 252 (accept_3_4 76 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 173 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 75 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 173 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 74 173 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 173 252 (accept_3_4 73 173 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 173 252 (Polychromatic418967fa.accept_16_8_13_12_1_3809 72 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 173 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 71 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 173 252 (accept_3_4 70 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 173 252 (Polychromatic418967fa.accept_27_15_11_9_1_15310 69 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 68 173 252 (Polychromatic418967fa.accept_16_4_13_12_1_1740 68 173 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 173 252 (accept_3_4 67 173 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 173 252 (Polychromatic418967fa.accept_13_1_4_5_1_113
  66 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 173 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 173 252 (accept_3_4 64 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 173 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 63 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 173 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 62 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 173 252 (accept_3_4 61 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 173 252 (Polychromatic418967fa.accept_19_3_2_5_1_5679 60 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 173 252
  (Polychromatic418967fa.accept_20_19_13_12_1_2476 59 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 173 252 (accept_3_4 58 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 173 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 173 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 252 (Polychromatic418967fa.accept_15_11_8_12_1_4437 56 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 173 252 (accept_3_4 55 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 173 252
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 54 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 173 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 53 173 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 252 (accept_3_4 52 173 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 173 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 252
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 50 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 252 (accept_3_4 49 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 48 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 252 (Polychromatic418967fa.accept_16_15_13_12_1_1787 47 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 252 (accept_3_4 46 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 252
  (Polychromatic418967fa.accept_24_20_5_12_1_6633 44 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 173 252 (accept_3_4 43 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 173 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 173 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 173 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 252 (accept_3_4 40 173 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 252
  (Polychromatic418967fa.accept_20_19_13_12_1_2476 39 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 38 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 252 (accept_3_4 37 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 252 (accept_3_4 34 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 32 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 252 (accept_3_4 31 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 252 (Polychromatic418967fa.accept_20_10_13_12_1_9726 30
  173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 252
  (Polychromatic418967fa.accept_19_10_2_5_1_3059 29 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 252 (accept_3_4 28 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 252 (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 252 (accept_3_4 25 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 252 (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 252 (accept_3_4 22 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 252 (accept_3_4 19 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 252 (accept_3_4 16 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 14 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 252 (accept_3_4 13 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 173
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 252 (accept_3_4 10 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 252 (Polychromatic418967fa.accept_16_8_13_12_1_3809 8 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 252 (accept_3_4 7 173 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 173 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 252 (accept_3_4 4 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 173 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 173 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 252 (accept_3_4 1 173 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 172 252 (Eq.refl Bool.true) (allA_succ_of_gcd 80 172 252 4 20 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 172 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 79 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 172 252 2 39 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 172 252 (accept_3_5 77 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 172 252 4 19 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 172 252 (Polychromatic418967fa.accept_19_18_1_5_1_5720 75 172 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 172 252 2 37 86 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 172 252
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 73 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 172 252 4 18 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 172 252 (accept_3_5 71 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 172 252 2 35 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 172 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 69 172 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 172 252 4 17 43 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 172 252
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 67 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 172 252 2 33 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 172 252 (accept_3_5 65 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 172 252 4 16 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 172 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 63 172 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 172 252 2 31 86 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 172 252
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 61 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 172 252 4 15 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 172 252 (accept_3_5 59 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 172 252 2 29 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 172 252 (Polychromatic418967fa.accept_25_7_22_2_1_13544 57 172 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 172 252 4 14 43 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 252
  (Polychromatic418967fa.accept_15_10_7_12_1_2490 55 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 172 252 2 27 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 172 252 (accept_3_5 53 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 172 252 4 13 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 172 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 51 172 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 252 2 25 86 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 252
  (Polychromatic418967fa.accept_15_4_7_12_1_5538 49 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 172 252 4 12 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 172 252 (accept_3_5 47 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 252 2 23 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 252 (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 172 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 252 4 11 43 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 252
  (Polychromatic418967fa.accept_22_21_18_10_1_5757 43 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 172 252 2 21 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 172 252 (accept_3_5 41 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 252 4 10 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 252 (Polychromatic418967fa.accept_17_5_2_14_1_4270 39 172 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 252 2 19 86 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 252
  (Polychromatic418967fa.accept_13_11_3_5_1_982 37 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 252 4 9 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 172 252 (accept_3_5 35 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  172 252 2 17 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 172 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 172 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 252 4 8 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 252 (Polychromatic418967fa.accept_19_12_1_5_1_9924
  31 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 252 2 15 86 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 252
  (accept_3_5 29 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 252 4 7 43 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 172 252 2 13 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 172 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 172 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 252 4 6 43 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 252 (accept_3_5 23 172 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 252 2 11 86 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 252
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 172 252 4 5 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 172 252 (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 172 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 172 252 2 9 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 172 252 (accept_3_5 17 172 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 172 252 4 4 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 172 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 172
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 252 2 7 86 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 252
  (Polychromatic418967fa.accept_24_13_4_12_1_15239 13 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 172 252 4 3 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 172 252 (accept_3_5 11 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 252 2 5 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 172 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 252 4 2 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 252
  (Polychromatic418967fa.accept_23_7_11_22_1_15375 7 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 172 252 2 3 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 172 252 (accept_3_5 5 172 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 172 252 4 1 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 172 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 172 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 172 252 2 1 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 1
  172 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 171 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 171 252 9 9 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 171 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 80 171 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 171 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 79 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 171 252 3 26 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 171 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 77 171 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 171 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 76 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 171 252 3 25 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 171 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 74 171 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 171 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 73 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 171 252 9 8 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 171 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 252 (Polychromatic418967fa.accept_15_10_6_12_1_1645 70 171
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 171 252 3 23 57 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 171 252
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 68 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 171 252 (Polychromatic418967fa.accept_15_7_6_12_1_1614 67 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 171 252 3 22 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 171 252 (Polychromatic418967fa.accept_15_5_6_12_1_916
  65 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 252
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 64 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 171 252 9 7 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 171 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 62 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 61 171
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 171 252 3 20 57 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 171 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 59 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 252 (Polychromatic418967fa.accept_16_10_11_12_1_4835 58 171 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 171 252 3 19 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 171 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 171 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 171 252 9 6 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 171 252 (Polychromatic418967fa.accept_10_3_1_2_1_521
  53 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 52 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 171 252 3 17 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 171 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 50 171 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 49 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 171 252 3 16 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 171 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 171 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 252 (Polychromatic418967fa.accept_10_6_1_2_1_874
  46 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 171 252 9 5 19 28
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 171 252
  (Polychromatic418967fa.accept_17_10_1_14_1_489 44 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 171 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 171 252 3 14 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 171 252
  (Polychromatic418967fa.accept_20_1_11_12_1_2467 41 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 171 252 (Polychromatic418967fa.accept_15_10_6_12_1_1645 40 171 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 171 252 3 13 57 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 171 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 171 252 (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 171 252 9 4 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310
  35 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 252
  (Polychromatic418967fa.accept_23_11_10_22_1_7017 34 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 171 252 3 11 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 171 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 32 171 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 171 252 3 10 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 171 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 171 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 252
  (Polychromatic418967fa.accept_22_6_17_10_1_12202 28 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 171 252 9 3 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 171 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 171 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 252
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 25 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 171 252 3 8 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 171 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 22 171
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 252 3 7 57 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 252
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 20 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 252 9 2 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045
  17 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 16 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 171 252 3 5 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 171 252 (Polychromatic418967fa.accept_25_14_21_2_1_15201 14 171 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 252 (Polychromatic418967fa.accept_10_3_1_2_1_521
  13 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 252 3 4 57 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 252
  (Polychromatic418967fa.accept_23_11_10_22_1_7017 11 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 171 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 252 9 1 19 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 252
  (Polychromatic418967fa.accept_16_8_11_12_1_962 8 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 252 3 2 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 171 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 252
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 171 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 171 252 3 1 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 171 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 171 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 252 (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 171
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 170 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 170 252 2 41 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 170 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 81 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 170 252 2 40 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 170 252 (accept_3_4 79 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 170 252 2 39 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 170 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 77 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 170 252 2 38 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 170 252 (Polychromatic418967fa.accept_16_11_10_12_1_4832 75 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 170 252 2 37 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 170 252 (accept_3_4 73 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 170 252 2 36 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 170 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 71 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 170 252 2 35 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 170 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 69 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 170 252 2 34 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 170 252 (accept_3_4 67 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 170 252 2 33 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 170 252
  (Polychromatic418967fa.accept_20_5_10_12_1_8200 65 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 170 252 2 32 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 170 252 (Polychromatic418967fa.accept_19_6_18_5_1_5630 63 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 170 252 2 31 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 170 252 (accept_3_4 61 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 170 252 2 30 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 170 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 59 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 170 252 2 29 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 170 252 (Polychromatic418967fa.accept_25_7_20_2_1_15228 57 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 170 252 2 28 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 170 252 (accept_3_4 55 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 170 252 2 27 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 170 252
  (Polychromatic418967fa.accept_15_8_5_12_1_4453 53 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 170 252 2 26 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 170 252 (Polychromatic418967fa.accept_13_12_1_5_1_1650 51 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 170 252 2 25 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 170 252 (accept_3_4 49 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 170 252 2 24 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 170 252
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 47 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 170 252 2 23 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 170 252 (Polychromatic418967fa.accept_13_6_1_5_1_3988 45 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 170 252 2 22 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 170 252 (accept_3_4 43 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 170 252 2 21 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 170 252
  (Polychromatic418967fa.accept_27_14_8_9_1_9614 41 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 170 252 2 20 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 170 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 170 252 2 19 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 170 252 (accept_3_4 37 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 170 252 2 18 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 170 252
  (Polychromatic418967fa.accept_13_9_1_5_1_964 35 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 170 252 2 17 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 170 252 (Polychromatic418967fa.accept_20_13_10_12_1_2462 33 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 170 252 2 16 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 170 252 (accept_3_4 31 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 170 252 2 15 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 170 252
  (Polychromatic418967fa.accept_13_3_1_5_1_499 29 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 170 252 2 14 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 170 252 (Polychromatic418967fa.accept_16_11_10_12_1_4832 27 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 170 252 2 13 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 170 252 (accept_3_4 25 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 170 252 2 12 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 170 252
  (Polychromatic418967fa.accept_15_8_5_12_1_4453 23 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 170 252 2 11 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 170 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 170 252 2 10 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 170 252 (accept_3_4 19 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 170 252 2 9 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 170 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 170 252 2 8 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 170 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 170 252 2 7 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 170 252 (accept_3_4 13 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 170 252 2 6 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 170 252
  (Polychromatic418967fa.accept_16_11_10_12_1_4832 11 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 170 252 2 5 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 170 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 170 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 252 2 4 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 252 (accept_3_4 7 170 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170 252 2 3 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 170 252
  (Polychromatic418967fa.accept_16_5_10_12_1_4904 5 170 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 170 252 2 2 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 170 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 170 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 252 2 1 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 252 (accept_3_4 1 170 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 170
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 169 252 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 169 252 (accept_3_5 83 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 169 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 82 169 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 169 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 81 169 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 169 252 (accept_3_5 80 169 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 169 252
  (Polychromatic418967fa.accept_17_11_16_14_1_6760 79 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 169 252 (Polychromatic418967fa.accept_19_2_17_5_1_5643 78 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 169 252 (accept_3_5 77 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 169 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 76 169
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 169 252
  (Polychromatic418967fa.accept_19_18_17_5_1_4343 75 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 169 252 (accept_3_5 74 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 169 252 (Polychromatic418967fa.accept_22_7_15_10_1_15374 73 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 169 252
  (Polychromatic418967fa.accept_16_8_9_12_1_1737 72 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 169 252 (accept_3_5 71 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 169 252 (Polychromatic418967fa.accept_17_2_16_14_1_2116 70 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 169 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 169 252 (accept_3_5 68 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 169 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 67 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 169 252
  (Polychromatic418967fa.accept_16_2_9_12_1_46 66 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 169 252 (accept_3_5 65 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 169 252 (Polychromatic418967fa.accept_19_7_17_5_1_3081 64 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 169 252 (Polychromatic418967fa.accept_20_3_9_12_1_6671 63 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 169 252 (accept_3_5 62 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 169 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 169 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 169 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 60 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 169 252 (accept_3_5 59 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 169 252 (Polychromatic418967fa.accept_22_14_15_10_1_12213 58 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 169 252 (accept_3_5 56 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 169 252 (Polychromatic418967fa.accept_22_11_15_10_1_9098 55
  169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 169 252
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 54 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 169 252 (accept_3_5 53 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 169 252 (Polychromatic418967fa.accept_15_7_4_12_1_2530 52 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 169 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 252 (accept_3_5 50 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 49 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 252
  (Polychromatic418967fa.accept_22_4_15_10_1_13730 48 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 169 252 (accept_3_5 47 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 169 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 46 169 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 169 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 252 (accept_3_5 44 169 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 252
  (Polychromatic418967fa.accept_20_3_9_12_1_6671 43 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 169 252 (Polychromatic418967fa.accept_17_8_16_14_1_4261 42 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 252 (accept_3_5 41 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 252 (Polychromatic418967fa.accept_16_8_9_12_1_1737 40 169 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 252
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 252 (accept_3_5 38 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 252 (Polychromatic418967fa.accept_16_4_9_12_1_4829 36 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 252 (accept_3_5 35 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 252 (Polychromatic418967fa.accept_16_2_9_12_1_46 34 169
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 252
  (Polychromatic418967fa.accept_19_14_17_5_1_15232 33 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 169 252 (accept_3_5 32 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 169 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 169 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 252 (Polychromatic418967fa.accept_19_11_17_5_1_8609 30 169
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 252 (accept_3_5 29 169
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 252
  (Polychromatic418967fa.accept_17_11_16_14_1_6760 28 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 252 (accept_3_5 26 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 252 (Polychromatic418967fa.accept_17_8_16_14_1_4261 25 169
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 252
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 24 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 252 (accept_3_5 23 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 252 (Polychromatic418967fa.accept_15_7_4_12_1_2530 22 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 252 (accept_3_5 20 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 252 (Polychromatic418967fa.accept_16_3_9_12_1_4831 19 169 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 252
  (Polychromatic418967fa.accept_16_2_9_12_1_46 18 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 252 (accept_3_5 17 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 252 (Polychromatic418967fa.accept_17_15_16_14_1_4291 15 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 252 (accept_3_5 14 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 169 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 252
  (Polychromatic418967fa.accept_19_12_17_5_1_5702 12 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 169 252 (accept_3_5 11 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 169 252 (Polychromatic418967fa.accept_25_10_19_2_1_4420 10 169 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611
  9 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 252 (accept_3_5 8
  169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 169 252 (Polychromatic418967fa.accept_22_6_15_10_1_10705 6 169 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 252 (accept_3_5 5 169 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 169 252 (Polychromatic418967fa.accept_16_4_9_12_1_4829 4 169 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 252
  (Polychromatic418967fa.accept_16_3_9_12_1_4831 3 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 252 (accept_3_5 2 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 169 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 168 252 (Eq.refl Bool.true) (allA_succ_of_gcd 84 168 252 84 1 2 3 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 168 252
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 83 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 168 252 2 41 84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 168 252 3 27 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 168 252 4 20 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 168 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 79 168
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 168 252 6 13 28 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 168 252 7 11 24 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 168 252 4 19 42
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 168 252 3 25
  56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 168 252 2
  37 84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 168
  252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 73 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 168 252 12 6 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 168 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 71 168 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 252 14 5 12 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 168 252 3 23 56 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 168 252 4 17 42 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 168 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 67 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 252 6 11 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 168 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 252 4 16 42 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 168 252 21 3 8 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 168 252 2 31 84 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 252
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 61 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 168 252 12 5 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 168 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603 59 168 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 252 2 29 84 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 168 252 3 19 56 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 168 252 28 2 6 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 55 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 252 6 9 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 168 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 53 168 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 252 4 13 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 168 252 3 17 56 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 168 252 2 25 84 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 168 252 7 7 24 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 168 252 12 4 14 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 252
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 47 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 168 252 2 23 84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 168 252 3 15 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 168 252 4 11 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 43 168
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 252 42 1 4 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 252 4 10 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 168 252 3 13 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 168 252 2 19 84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 168
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 252 12 3 14 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 168 252 7 5 24 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 168 252 2 17 84 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 168 252 3 11 56
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 168 252 4 8 42
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 252
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 31 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 168 252 6 5 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 168 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 168 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 252 28 1 6 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 168 252 3 9 56 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 168 252 2 13 84 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 252 12 2 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 168 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 252 2 11 84 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 168 252 21 1 8 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 252 4 5 42 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 252 6 3 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 168 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 252 4 4 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 168 252 3 5 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 252 14 1 12 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 168 252 12 1 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 168 252 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 168 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 252 2 5 84 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 168 252 3 3 56 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 168 252 4 2 42 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 168 252 7 1 24 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 168 252 6 1 28 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 168 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 168 252 4 1 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 168 252 3 1 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 168 252 2 1 84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 168 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 168 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 167 252
  (Eq.refl Bool.true) (allA_succ_of_accept 85 167 252 (accept_3_4 85 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 167 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 167 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 167 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 83 167 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 167 252 (accept_3_4 82 167 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 167 252
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 81 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 167 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 80 167 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 167 252 (accept_3_4 79 167 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 167 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 78 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 167 252
  (Polychromatic418967fa.accept_19_1_15_5_1_4357 77 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 167 252 (accept_3_4 76 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 167 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 167 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 167 252 (accept_3_4 73 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 167 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 72 167
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 167 252
  (Polychromatic418967fa.accept_13_6_11_5_1_133 71 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 167 252 (accept_3_4 70 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 167 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 69 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 167 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 68 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 252 (accept_3_4 67 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 66 167
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 65 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 167 252 (accept_3_4 64 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 167 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 63 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 167 252 (Polychromatic418967fa.accept_20_2_7_12_1_5215 62 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 252 (accept_3_4 61 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 252 (Polychromatic418967fa.accept_25_10_17_2_1_15307 60
  167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 252 (accept_3_4 58 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 252 (Polychromatic418967fa.accept_20_17_7_12_1_6632 57 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 252 (accept_3_4 55 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 167
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 252
  (Polychromatic418967fa.accept_16_5_7_12_1_7206 53 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 252 (accept_3_4 52 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 50 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 252 (accept_3_4 49 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 167
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 252
  (Polychromatic418967fa.accept_19_9_15_5_1_5666 47 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 252 (accept_3_4 46 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 252 (accept_3_4 43 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 42 167
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 252
  (Polychromatic418967fa.accept_22_19_13_10_1_12177 41 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 167 252 (accept_3_4 40 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 167 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 167 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 252 (Polychromatic418967fa.accept_27_11_5_9_1_11493 38 167
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 252 (accept_3_4 37 167
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 252
  (Polychromatic418967fa.accept_15_6_2_12_1_885 36 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 167 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 167 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 252 (accept_3_4 34 167 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 167 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 252
  (Polychromatic418967fa.accept_13_6_11_5_1_133 32 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 252 (accept_3_4 31 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 252 (Polychromatic418967fa.accept_19_11_15_5_1_5699 30 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 252 (accept_3_4 28 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 167 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 252
  (Polychromatic418967fa.accept_20_6_7_12_1_8197 26 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 252 (accept_3_4 25 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 252 (accept_3_4 22 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 167
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 252
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 252 (accept_3_4 19 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 252 (Polychromatic418967fa.accept_19_17_15_5_1_7096 17 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 252 (accept_3_4 16 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 167
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 252 (accept_3_4 13 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 167 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 252 (accept_3_4 10 167 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 252
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 252 (accept_3_4 7 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 167 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 252 (accept_3_4 4 167 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 167 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 252
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 2 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 252 (accept_3_4 1 167 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 166 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 166 252 2 43 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 166 252 (Polychromatic418967fa.accept_19_9_14_5_1_1890 85 166
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 166 252 2 42 83 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 166 252 (accept_3_5 83
  166 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 166 252 2 41 83 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 166 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 166 252 2 40 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 166 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 79 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 166 252 2 39 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 166 252 (accept_3_5 77 166 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 166 252 2 38 83 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 166 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 75 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 166 252 2 37 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 166 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 73 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 166 252 2 36 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 166 252 (accept_3_5 71 166 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 166 252 2 35 83 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 166 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 69 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 166 252 2 34 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 166 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 67 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 166 252 2 33 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 166 252 (accept_3_5 65 166 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 166 252 2 32 83 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 166 252
  (Polychromatic418967fa.accept_19_6_14_5_1_4339 63 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 166 252 2 31 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 166 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 61 166 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 166 252 2 30 83 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 166 252 (accept_3_5 59 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 166 252 2 29 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 166 252 (Polychromatic418967fa.accept_11_2_1_10_1_196
  57 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 252 2 28 83 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 252
  (Polychromatic418967fa.accept_17_4_13_14_1_1139 55 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 166 252 2 27 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 166 252 (accept_3_5 53 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 252 2 26 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 166 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 252 2 25 83 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 252
  (Polychromatic418967fa.accept_15_4_1_12_1_914 49 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 252 2 24 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 252 (accept_3_5 47 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 252 2 23 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 252 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 252 2 22 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 43 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 252 2 21 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 252 (accept_3_5 41 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 252 2 20 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 252 (Polychromatic418967fa.accept_25_14_16_2_1_15373 39 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 252 2 19 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 252
  (Polychromatic418967fa.accept_20_17_6_12_1_8185 37 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 166 252 2 18 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 166 252 (accept_3_5 35 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 252 2 17 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 252 (Polychromatic418967fa.accept_22_11_12_10_1_1424 33 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 252 2 16 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 252 2 15 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 252 (accept_3_5 29 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 252 2 14 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 252 (Polychromatic418967fa.accept_17_10_13_14_1_3094 27 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 252 2 13 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 252
  (Polychromatic418967fa.accept_19_6_14_5_1_4339 25 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 252 2 12 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 252 (accept_3_5 23 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 252 2 11 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 166 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 252 2 10 83 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 252 2 9 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 252 (accept_3_5 17 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 252 2 8 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 252 2 7 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 13 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 252 2 6 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 252 (accept_3_5 11 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 252 2 5 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 166 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 252 2 4 83 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 252
  (Polychromatic418967fa.accept_20_7_6_12_1_6650 7 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 252 2 3 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 252 (accept_3_5 5 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  252 2 2 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 252 (Polychromatic418967fa.accept_19_3_14_5_1_8597 3 166 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 252 2 1 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 166 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 165 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 165 252 3 29 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 165 252 (Polychromatic418967fa.accept_19_10_13_5_1_3091 86 165
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 165 252
  (Polychromatic418967fa.accept_19_9_13_5_1_4351 85 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 165 252 3 28 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 165 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 83 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 165 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641
  82 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 165 252 3 27 55 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 165 252
  (Polychromatic418967fa.accept_13_2_9_5_1_959 80 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 165 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 79 165 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 165 252 3 26 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 165 252 (Polychromatic418967fa.accept_10_7_5_2_1_880
  77 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 165 252
  (Polychromatic418967fa.accept_25_1_15_2_1_15372 76 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 165 252 3 25 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 165 252 (Polychromatic418967fa.accept_16_10_5_12_1_4925 74 165 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 73 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 165 252 3 24 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 165 252 (Polychromatic418967fa.accept_16_7_5_12_1_4824 71 165 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 252
  (Polychromatic418967fa.accept_20_10_5_12_1_13866 70 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 165 252 3 23 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 165 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 68 165 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 67 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 165 252 3 22 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 165 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 252
  (Polychromatic418967fa.accept_19_7_13_5_1_7125 64 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 165 252 3 21 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 165 252 (Polychromatic418967fa.accept_17_11_12_14_1_5431 62 165 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 252
  (Polychromatic418967fa.accept_25_11_15_2_1_15371 61 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 165 252 3 20 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 165 252 (Polychromatic418967fa.accept_22_15_11_10_1_15317 59 165 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 58 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 165 252 3 19 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 165 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 56 165 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 55 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 165 252 3 18 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 165 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 53 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 252
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 52 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 165 252 3 17 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 165 252 (Polychromatic418967fa.accept_19_12_13_5_1_11331 50 165 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 49 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 165 252 3 16 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 165 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 47 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 252
  (Polychromatic418967fa.accept_19_8_13_5_1_1889 46 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 165 252 3 15 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 165 252 (Polychromatic418967fa.accept_23_21_4_22_1_15311 44 165 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 43 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 165 252 3 14 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 165 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598
  40 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 165 252 3 13 55 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 165 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 252 3 12 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 165 252
  (Polychromatic418967fa.accept_20_15_5_12_1_15225 35 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 165 252 (Polychromatic418967fa.accept_22_12_11_10_1_15342 34 165 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 252 3 11 55 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 252
  (Polychromatic418967fa.accept_17_15_12_14_1_2087 32 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 165 252 (Polychromatic418967fa.accept_19_12_13_5_1_11331 31 165 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 252 3 10 55 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 29 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 165 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 252 3 9 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 252
  (Polychromatic418967fa.accept_16_10_5_12_1_4925 26 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 165 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 252 3 8 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 252 (Polychromatic418967fa.accept_26_22_9_18_1_7923 22 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 165 252 3 7 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 165 252
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 20 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 252 (Polychromatic418967fa.accept_22_19_11_10_1_5825 19 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 252 3 6 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 165 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 252 3 5 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598
  14 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 13 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 165 252 3 4 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 165 252 (Polychromatic418967fa.accept_17_11_12_14_1_5431 11 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 252
  (Polychromatic418967fa.accept_16_10_5_12_1_4925 10 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 165 252 3 3 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 165 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 165 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 7
  165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 252 3 2 55 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 252
  (Polychromatic418967fa.accept_23_5_4_22_1_15230 5 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 165 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 252 3 1 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 2 165 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 165 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  89 164 252 (Eq.refl Bool.true) (allA_succ_of_gcd 88 164 252 4 22 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 164 252 (Polychromatic418967fa.accept_10_7_4_2_1_903
  87 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 164 252 2 43 82 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 164 252
  (accept_3_4 85 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 164 252 4 21 41 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 164 252
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 83 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 164 252 2 41 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 164 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 81 164 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 164 252 4 20 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 164 252 (accept_3_4 79 164 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 164 252 2 39 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 164 252 (Polychromatic418967fa.accept_10_7_4_2_1_903
  77 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 164 252 4 19 41 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 164 252
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 75 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 164 252 2 37 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 164 252 (accept_3_4 73 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 164 252 4 18 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 164 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 71 164 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 252 2 35 82 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 252
  (Polychromatic418967fa.accept_15_9_14_12_1_913 69 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 252 4 17 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 252 (accept_3_4 67 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 252 2 33 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 252 (Polychromatic418967fa.accept_16_1_4_12_1_376 65 164 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 252 4 16 41 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 252
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 164 252 2 31 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 164 252 (accept_3_4 61 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 252 4 15 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 252 (Polychromatic418967fa.accept_16_11_4_12_1_1760 59 164 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 252 2 29 82 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 252 4 14 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 252 (accept_3_4 55 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 252 2 27 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 53 164 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 252 4 13 41 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 252
  (Polychromatic418967fa.accept_13_12_8_5_1_976 51 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 252 2 25 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 252 (accept_3_4 49 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 252 4 12 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 164 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 252 2 23 82 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 252
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 164 252 4 11 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 164 252 (accept_3_4 43 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 252 2 21 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 41 164 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 252 4 10 41 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 252
  (Polychromatic418967fa.accept_15_9_14_12_1_913 39 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 252 2 19 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 252 (accept_3_4 37 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 252 4 9 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 35 164 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 252 2 17 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 252 (Polychromatic418967fa.accept_16_1_4_12_1_376
  33 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 252 4 8 41 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 252
  (accept_3_4 31 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 252 2 15 82 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 252
  (Polychromatic418967fa.accept_13_3_8_5_1_974 29 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 164 252 4 7 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 164 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 164 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 252 2 13 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 252 (accept_3_4 25 164 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 252 4 6 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 164
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 252 2 11 82 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 252
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 252 4 5 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 164 252 (accept_3_4 19 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  164 252 2 9 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 164 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 164 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 252 4 4 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 252
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 164 252 2 7 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 164 252 (accept_3_4 13 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 252 4 3 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 164 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 164 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 252 2 5 82 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 252
  (Polychromatic418967fa.accept_15_9_14_12_1_913 9 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 252 4 2 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 252 (accept_3_4 7 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  252 2 3 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 252 (Polychromatic418967fa.accept_16_5_4_12_1_3800 5 164 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 252 4 1 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 164 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 3 164 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 252 2 1 82 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 252 (accept_3_4 1 164 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 164
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 163 252
  (Eq.refl Bool.true) (allA_succ_of_accept 89 163 252 (accept_3_5 89 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 163 252 (Polychromatic418967fa.accept_16_8_3_12_1_1819 88 163 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 163 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 163 252 (accept_3_5 86 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 163 252 (Polychromatic418967fa.accept_10_5_3_2_1_899
  85 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 163 252
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 84 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 163 252 (accept_3_5 83 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 163 252 (Polychromatic418967fa.accept_19_6_11_5_1_5628 82 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 163 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 81 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 163 252 (accept_3_5 80 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 163 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 79 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 163 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 78 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 163 252 (accept_3_5 77 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 163 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 76 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 163 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 75 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 163 252 (accept_3_5 74 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 163 252 (Polychromatic418967fa.accept_16_9_3_12_1_1802 73 163
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 163 252
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 72 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 163 252 (accept_3_5 71 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 163 252 (Polychromatic418967fa.accept_15_10_13_12_1_3384 70 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 252 (Polychromatic418967fa.accept_17_1_10_14_1_1173 69 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 163 252 (accept_3_5 68 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 163 252 (Polychromatic418967fa.accept_11_1_9_10_1_184
  67 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 252
  (Polychromatic418967fa.accept_23_20_2_22_1_15370 66 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 163 252 (accept_3_5 65 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 163 252 (Polychromatic418967fa.accept_13_12_7_5_1_3147 64 163 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 252 (accept_3_5 62 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 163 252 (Polychromatic418967fa.accept_10_1_3_2_1_220
  61 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 252
  (Polychromatic418967fa.accept_27_6_1_9_1_15369 60 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 163 252 (accept_3_5 59 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 163 252 (Polychromatic418967fa.accept_16_10_3_12_1_1758 58 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 252 (Polychromatic418967fa.accept_16_9_3_12_1_1802 57 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 252 (accept_3_5 56 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 252
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 252 (accept_3_5 53 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 52 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 252 (accept_3_5 50 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 252 (Polychromatic418967fa.accept_20_9_3_12_1_6627 49 163
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 48 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 252 (accept_3_5 47 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 252 (Polychromatic418967fa.accept_15_1_13_12_1_347 46 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 252 (accept_3_5 44 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 252 (Polychromatic418967fa.accept_22_21_9_10_1_15312 43
  163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 252
  (Polychromatic418967fa.accept_16_10_3_12_1_1758 42 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 163 252 (accept_3_5 41 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 163 252 (Polychromatic418967fa.accept_15_10_13_12_1_3384 40 163 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 252 (Polychromatic418967fa.accept_8_7_3_4_1_404
  39 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 252 (accept_3_5 38
  163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 252
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 163 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 36 163 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 252 (accept_3_5 35 163 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 163 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 34 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 33 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 252 (accept_3_5 32 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 252 (accept_3_5 29 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 28 163
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 252
  (Polychromatic418967fa.accept_22_5_9_10_1_15207 27 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 163 252 (accept_3_5 26 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 163 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 163 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 163
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 252 (accept_3_5 23 163
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 252
  (Polychromatic418967fa.accept_17_5_10_14_1_2083 22 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 252 (accept_3_5 20 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 163
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 18 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 252 (accept_3_5 17 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 252 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 163 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 252 (accept_3_5 14 163 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 252 (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 12 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 252 (accept_3_5 11 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 252 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 252 (Polychromatic418967fa.accept_16_9_3_12_1_1802 9 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 252 (accept_3_5 8 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 252
  (Polychromatic418967fa.accept_19_6_11_5_1_5628 6 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 252 (accept_3_5 5 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 4 163 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 252 (accept_3_5 2 163 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 163 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 162 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 162 252 18 5 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 162 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 89 162 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 162 252 2 44 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 162 252 3 29 54 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 162 252 2 43 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 162 252
  (Polychromatic418967fa.accept_22_19_8_10_1_12142 85 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 162 252 6 14 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 162 252 (Polychromatic418967fa.accept_19_7_10_5_1_3090 83 162 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 162 252 2 41 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 162 252 9 9 18 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 162 252 2 40 81 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 162 252
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 79 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 252 6 13 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 77 162 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 162 252 2 38 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 162 252 3 25 54 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 162 252 2 37 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 162 252
  (Polychromatic418967fa.accept_16_9_2_12_1_1800 73 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 252 18 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 162 252 (Polychromatic418967fa.accept_16_7_2_12_1_1754 71 162 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 252 2 35 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 162 252 3 23 54 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 162 252 2 34 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 252
  (Polychromatic418967fa.accept_20_7_2_12_1_6642 67 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 252 6 11 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 252 (Polychromatic418967fa.accept_16_1_2_12_1_1757 65 162 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 252 2 32 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 162 252 9 7 18 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 162 252 2 31 81 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 252
  (Polychromatic418967fa.accept_23_15_1_22_1_13711 61 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 162 252 6 10 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 162 252 (Polychromatic418967fa.accept_19_2_10_5_1_5639 59 162 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 252 2 29 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 162 252 3 19 54 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 162 252 2 28 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 252
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 55 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 252 18 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 162 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 53 162 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 252 2 26 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 162 252 3 17 54 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 162 252 2 25 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 252
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 49 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 252 6 8 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 162 252 (Polychromatic418967fa.accept_16_15_2_12_1_1799 47 162 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 252 2 23 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 162 252 9 5 18 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 252 2 22 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 252
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 43 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 252 6 7 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 162 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800 41 162 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 252 2 20 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 162 252 3 13 54 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 162 252 2 19 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 252
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 37 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 252 18 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 162 252 (Polychromatic418967fa.accept_19_16_10_5_1_7106 35 162 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 252 2 17 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 162 252 3 11 54 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 252 2 16 81 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 252
  (Polychromatic418967fa.accept_11_9_8_10_1_934 31 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 252 6 5 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 162 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 162 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 252 2 14 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 252 9 3 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 252 2 13 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 252
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 252 6 4 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 162 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 162 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 252 2 11 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 252 3 7 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 252 2 10 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 252
  (Polychromatic418967fa.accept_20_19_2_12_1_2516 19 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 162 252 18 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 162 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 162 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 252 2 8 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 252 3 5 54 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 252 2 7 81 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 252
  (Polychromatic418967fa.accept_19_13_10_5_1_11329 13 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 252 6 2 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 162 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 252 2 5 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 252 9 1 18 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 252 2 4 81 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 252
  (Polychromatic418967fa.accept_16_7_2_12_1_1754 7 162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 252 6 1 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 252 (Polychromatic418967fa.accept_17_5_9_14_1_4282 5 162 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 252 2 2 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 252 3 1 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 252 2 1 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 1
  162 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 161 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 161 252 7 13 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 161 252 (Polychromatic418967fa.accept_19_14_9_5_1_9941 90 161
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 161 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 89 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 161 252 (accept_3_4 88 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 161 252 (Polychromatic418967fa.accept_22_21_7_10_1_5821 87 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 161 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 86 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 161 252 (accept_3_4 85 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 161 252 7 12 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 161 252 (Polychromatic418967fa.accept_10_3_1_2_1_521
  83 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 252 (accept_3_4 82
  161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 161 252
  (Polychromatic418967fa.accept_22_15_7_10_1_15368 81 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 161 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 80 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 161 252 (accept_3_4 79 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 161 252 (Polychromatic418967fa.accept_22_12_7_10_1_15184 78
  161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 161 252 7 11 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 161 252 (accept_3_4 76
  161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 252
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 75 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 161 252 (Polychromatic418967fa.accept_15_14_11_12_1_4440 74 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 161 252 (accept_3_4 73 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 161 252 (Polychromatic418967fa.accept_16_8_1_12_1_984 72 161
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 161 252
  (Polychromatic418967fa.accept_19_14_9_5_1_9941 71 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 161 252 7 10 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 161 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 252
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 68 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 161 252 (accept_3_4 67 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 161 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 161 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 161 252 (Polychromatic418967fa.accept_22_21_7_10_1_5821 65 161
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 252 (accept_3_4 64 161
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 161 252 7 9 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 161 252
  (Polychromatic418967fa.accept_17_11_8_14_1_8084 62 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 161 252 (accept_3_4 61 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 161 252 (Polychromatic418967fa.accept_22_16_7_10_1_7356 60 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 161 252 (Polychromatic418967fa.accept_10_9_1_2_1_522
  59 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 252 (accept_3_4 58
  161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 252
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 57 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 161 252 7 8 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 161 252 (accept_3_4 55 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 252 (Polychromatic418967fa.accept_24_6_17_12_1_6681 54 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 252 (accept_3_4 52 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 252 (Polychromatic418967fa.accept_19_13_9_5_1_8541 51 161 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 252
  (Polychromatic418967fa.accept_16_2_1_12_1_3798 50 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 161 252 7 7 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 161 252 (Polychromatic418967fa.accept_22_4_7_10_1_12171 48 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 252 (Polychromatic418967fa.accept_11_3_7_10_1_180
  47 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 252 (accept_3_4 46
  161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 161 252 (Polychromatic418967fa.accept_15_14_11_12_1_4440 44 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 252 (accept_3_4 43 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 161 252 7 6 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 161 252 (Polychromatic418967fa.accept_17_7_8_14_1_6720 41 161
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 252 (accept_3_4 40 161
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 39 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 161 252 (Polychromatic418967fa.accept_15_8_11_12_1_1626 38 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 252 (accept_3_4 37 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 161 252 7 5 23 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 161 252 (accept_3_4 34 161 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 252 (Polychromatic418967fa.accept_10_3_1_2_1_521
  33 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 252
  (Polychromatic418967fa.accept_19_13_9_5_1_8541 32 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 252 (accept_3_4 31 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 252 (Polychromatic418967fa.accept_22_8_7_10_1_10702 30 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 161 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 161 252 7 4 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 161 252
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 27 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 252 (accept_3_4 25 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 252 (Polychromatic418967fa.accept_16_8_1_12_1_984 24 161
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 252 (accept_3_4 22 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  161 252 7 3 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 161 252 (Polychromatic418967fa.accept_16_4_1_12_1_1792 20 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 161 252 (accept_3_4 19 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 161 252 (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 161 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 252 (Polychromatic418967fa.accept_22_17_7_10_1_15304 17
  161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 252 (accept_3_4 16
  161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 252
  (Polychromatic418967fa.accept_19_15_9_5_1_5656 15 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 161 252 7 2 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 161 252 (accept_3_4 13 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 252 (Polychromatic418967fa.accept_19_12_9_5_1_8593 12 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 252 (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 252 (accept_3_4 10 161 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 161 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 252
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 161 252 7 1 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 161 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 161 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 161 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 252 (accept_3_4 4 161 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 3
  161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 252
  (Polychromatic418967fa.accept_16_2_1_12_1_3798 2 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 252 (accept_3_4 1 161 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 160 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 160 252 4 23 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 160 252 (Polychromatic418967fa.accept_17_6_7_14_1_6704 91 160
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 160 252 2 45 80 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 160 252 (accept_3_5 89
  160 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 160 252 4 22 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 160 252
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 87 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 160 252 2 43 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 160 252 (Polychromatic418967fa.accept_24_13_16_12_1_10137 85 160 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 160 252 4 21 40 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 160 252 (accept_3_5 83 160 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 160 252 2 41 80 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 160 252
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 81 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 160 252 4 20 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 160 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 79 160 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 160 252 2 39 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 160 252 (accept_3_5 77 160 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 160 252 4 19 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 160 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 75 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 160 252 2 37 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 160 252 (Polychromatic418967fa.accept_15_13_10_12_1_2503 73 160 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 160 252 4 18 40 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 160 252 (accept_3_5 71 160 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 160 252 2 35 80 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 160 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 69 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 160 252 4 17 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 160 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 67 160 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 160 252 2 33 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 160 252 (accept_3_5 65 160 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 160 252 4 16 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 160 252
  (Polychromatic418967fa.accept_26_11_4_18_1_15367 63 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 160 252 2 31 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 160 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 61 160 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 160 252 4 15 40 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 160 252 (accept_3_5 59 160 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 160 252 2 29 80 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 160 252
  (Polychromatic418967fa.accept_17_6_7_14_1_6704 57 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 160 252 4 14 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 160 252 (Polychromatic418967fa.accept_17_4_7_14_1_10583 55 160 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 160 252 2 27 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 160 252 (accept_3_5 53 160 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 160 252 4 13 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 160 252
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 51 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 160 252 2 25 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 160 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 160 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 160 252 4 12 40 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 160 252 (accept_3_5 47 160 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 160 252 2 23 80 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 160 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 160 252 4 11 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 160 252 (Polychromatic418967fa.accept_15_13_10_12_1_2503 43 160 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 160 252 2 21 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 160 252 (accept_3_5 41 160 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 160 252 4 10 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 160 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 160 252 2 19 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 160 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 37 160 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 160 252 4 9 40 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 160 252 (accept_3_5 35
  160 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 160 252 2 17 80 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 160 252
  (Polychromatic418967fa.accept_19_14_8_5_1_8606 33 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 160 252 4 8 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 160 252 (Polychromatic418967fa.accept_19_12_8_5_1_8538 31 160 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 252 2 15 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 252 (accept_3_5 29 160 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 252 4 7 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 160
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 252 2 13 80 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 252
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 252 4 6 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 160 252 (accept_3_5 23 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  160 252 2 11 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 160 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 160 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 252 4 5 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 252 2 9 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 160 252 (accept_3_5 17 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 252 4 4 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 160 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 160 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 252 2 7 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 252
  (Polychromatic418967fa.accept_15_13_10_12_1_2503 13 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 160 252 4 3 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 160 252 (accept_3_5 11 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 252 2 5 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 160 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 160 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 252 4 2 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403
  7 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 252 2 3 80 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 252 (accept_3_5 5
  160 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 252 4 1 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 252
  (Polychromatic418967fa.accept_19_3_8_5_1_1875 3 160 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 160 252 2 1 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 160 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 160 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 160
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 159
  252 (Eq.refl Bool.true) (allA_succ_of_gcd 93 159 252 3 31 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 159 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 92 159
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 91 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 159 252 3 30 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 159 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 89 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 159 252
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 88 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 159 252 3 29 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 159 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 86 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 252
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 85 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 159 252 3 28 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 159 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 83 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 159 252
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 82 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 81 159 252 3 27 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 159 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 80 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 79 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 159 252 3 26 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 159 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 77 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 252
  (Polychromatic418967fa.accept_13_11_3_5_1_982 76 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 159 252 3 25 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 159 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 74 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 252
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 73 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 159 252 3 24 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 159 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 71 159 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 252 (Polychromatic418967fa.accept_11_4_5_10_1_926
  70 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 159 252 3 23 53 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 159 252
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 68 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 159 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 159 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 159 252 3 22 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 159 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 65 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 159 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 64 159 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 159 252 3 21 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 159 252
  (Polychromatic418967fa.accept_20_2_19_12_1_2500 62 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 159 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 61 159 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 159 252 3 20 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 159 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 159 252 (Polychromatic418967fa.accept_13_6_3_5_1_3167 58 159 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 159 252 3 19 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 159 252
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 56 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 159 252 (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 159 252 3 18 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 159 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 53 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 252 (Polychromatic418967fa.accept_16_4_15_12_1_1745 52 159 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 159 252 3 17 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 159 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 50 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 49 159 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 159 252 3 16 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 159 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887
  47 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 252
  (Polychromatic418967fa.accept_22_2_5_10_1_13757 46 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 159 252 3 15 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 159 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498 44 159 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 159 252 3 14 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 159 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 41 159 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 252 (Polychromatic418967fa.accept_13_1_3_5_1_140
  40 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 159 252 3 13 53 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 159 252
  (Polychromatic418967fa.accept_22_16_5_10_1_10671 38 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 159 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 159 252 3 12 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 159 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 34 159 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 159 252 3 11 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 159 252 (Polychromatic418967fa.accept_13_6_3_5_1_3167
  32 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 31 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 159 252 3 10 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 159 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 28 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 159 252 3 9 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 159 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 159 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 252 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 159
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 252 3 8 53 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 252
  (Polychromatic418967fa.accept_22_1_5_10_1_10706 23 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 159 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 22 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 252 3 7 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 159 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 252 3 6 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887
  17 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 252
  (Polychromatic418967fa.accept_22_16_5_10_1_10671 16 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 159 252 3 5 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 159 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 14 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 252
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 159 252 3 4 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 159 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 159 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 252
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 159 252 3 3 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 159 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 159 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887
  7 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 252 3 2 53 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 159 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 252 3 1 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 159 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 1 159 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 159 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 95 158 252 (Eq.refl Bool.true) (allA_succ_of_gcd 94 158 252 2 47 79 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 158 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 93 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 158 252 2 46 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 158 252 (accept_3_4 91 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 158 252 2 45 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 158 252 (Polychromatic418967fa.accept_27_8_23_9_1_11584 89 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 158 252 2 44 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 158 252
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 87 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 158 252 2 43 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 158 252 (accept_3_4 85 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 158 252 2 42 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 158 252 (Polychromatic418967fa.accept_19_7_6_5_1_4320 83 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 158 252 2 41 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 252
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 81 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 158 252 2 40 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 158 252 (accept_3_4 79 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 158 252 2 39 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 158 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 77 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 252 2 38 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 75 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 158 252 2 37 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 252 (accept_3_4 73 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 252 2 36 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 71 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 252 2 35 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 252
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 69 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 252 2 34 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 252 (accept_3_4 67 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 252 2 33 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 158 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 252 2 32 79 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 252
  (Polychromatic418967fa.accept_15_3_8_12_1_900 63 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 252 2 31 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 252 (accept_3_4 61 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 252 2 30 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 252 (Polychromatic418967fa.accept_13_7_2_5_1_2344 59 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 252 2 29 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 252
  (Polychromatic418967fa.accept_23_11_20_22_1_7070 57 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 158 252 2 28 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 158 252 (accept_3_4 55 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 252 2 27 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 252 (Polychromatic418967fa.accept_17_2_5_14_1_2068 53 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 252 2 26 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 252
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 51 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 252 2 25 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 252 (accept_3_4 49 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 252 2 24 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 252 (Polychromatic418967fa.accept_27_20_23_9_1_9594 47 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 252 2 23 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 252 2 22 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 252 (accept_3_4 43 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 252 2 21 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 252 (Polychromatic418967fa.accept_15_11_8_12_1_4437 41 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 252 2 20 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 252
  (Polychromatic418967fa.accept_19_1_6_5_1_4319 39 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 252 2 19 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 252 (accept_3_4 37 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 252 2 18 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 158 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 252 2 17 79 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 252
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 252 2 16 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 252 (accept_3_4 31 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 252 2 15 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 29 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 252 2 14 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 252 2 13 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 252 (accept_3_4 25 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 252 2 12 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 252 2 11 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 252
  (Polychromatic418967fa.accept_23_21_20_22_1_15256 21 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 158 252 2 10 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 158 252 (accept_3_4 19 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 252 2 9 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 252 2 8 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 252 2 7 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 252 (accept_3_4 13 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 252 2 6 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 252 (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 252 2 5 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 252
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 252 2 4 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 252 (accept_3_4 7 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  252 2 3 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 158 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 252 2 2 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 158 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 252 2 1 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 252 (accept_3_4 1 158 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 157
  252 (Eq.refl Bool.true) (allA_succ_of_accept 95 157 252 (accept_3_5 95 157 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 157 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 94 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 157 252
  (Polychromatic418967fa.accept_15_3_7_12_1_372 93 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 157 252 (accept_3_5 92 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 157 252 (Polychromatic418967fa.accept_27_10_22_9_1_15366 91 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 157 252 (Polychromatic418967fa.accept_13_12_1_5_1_1650 90 157 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 157 252 (accept_3_5 89 157 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 157 252
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 88 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 157 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 87 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 157 252 (accept_3_5 86 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 157 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 85 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 157 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 84 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 157 252 (accept_3_5 83 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 157 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 82 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 157 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 157 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 157 252 (accept_3_5 80 157 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 157 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 79 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 157 252
  (Polychromatic418967fa.accept_15_3_7_12_1_372 78 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 157 252 (accept_3_5 77 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 157 252 (Polychromatic418967fa.accept_24_4_13_12_1_6677 76 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 157 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 75 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 252 (accept_3_5 74 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 157 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 252
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 72 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 157 252 (accept_3_5 71 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 157 252 (Polychromatic418967fa.accept_15_10_7_12_1_2490 70 157 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 157 252 (Polychromatic418967fa.accept_10_9_7_2_1_887
  69 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 252 (accept_3_5 68
  157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 252
  (Polychromatic418967fa.accept_20_7_17_12_1_11156 67 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 157 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 66 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 252 (accept_3_5 65 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 252
  (Polychromatic418967fa.accept_15_3_7_12_1_372 63 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 252 (accept_3_5 62 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 61 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 157 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176 60 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 252 (accept_3_5 59 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 252 (Polychromatic418967fa.accept_13_6_1_5_1_3988 58 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 57 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 252 (accept_3_5 56 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 252 (accept_3_5 53 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 252 (Polychromatic418967fa.accept_16_4_13_12_1_1740 52 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 252 (accept_3_5 50 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 48 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 252 (accept_3_5 47 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 252 (Polychromatic418967fa.accept_20_6_17_12_1_8210 46 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 45 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 252 (accept_3_5 44 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 43 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 252 (accept_3_5 41 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 40 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 39 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 252 (accept_3_5 38 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 252 (Polychromatic418967fa.accept_22_15_3_10_1_15365 37 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 36 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 252 (accept_3_5 35 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 252 (accept_3_5 32 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 252 (Polychromatic418967fa.accept_16_15_13_12_1_1787 31 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 252 (accept_3_5 29 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 252 (Polychromatic418967fa.accept_22_6_3_10_1_12182 28 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 252
  (Polychromatic418967fa.accept_20_7_17_12_1_11156 27 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 157 252 (accept_3_5 26 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 157 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 157 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 252 (accept_3_5 23 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 252
  (Polychromatic418967fa.accept_13_9_1_5_1_964 22 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 157 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 157 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 252 (accept_3_5 20 157 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 157 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 252 (accept_3_5 17 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 252 (accept_3_5 14 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 252 (Polychromatic418967fa.accept_17_13_4_14_1_4272 13 157
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 252 (accept_3_5 11 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 252 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 157 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 252 (accept_3_5 8 157 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 6 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 252 (accept_3_5 5 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 157 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 157 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 252 (accept_3_5 2 157 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 157 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 156
  252 (Eq.refl Bool.true) (allA_succ_of_gcd 96 156 252 12 8 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 156 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 95 156
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 156 252 2 47 78 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 156 252 3 31 52 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 156 252 4 23 39
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 156 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 91 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 156 252 6 15 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 156 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 89 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 156 252 4 22 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 156 252 3 29 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 156 252 2 43 78 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 156 252
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 85 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 156 252 12 7 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 156 252 (Polychromatic418967fa.accept_17_15_3_14_1_4230 83 156 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 156 252 2 41 78 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 156 252 3 27 52 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 156 252 4 20 39
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 156 252
  (Polychromatic418967fa.accept_17_11_3_14_1_6736 79 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 156 252 6 13 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 156 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 77 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 156 252 4 19 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 156 252 3 25 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 156 252 2 37 78 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 252
  (Polychromatic418967fa.accept_23_4_18_22_1_8773 73 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 156 252 12 6 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 156 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 252 2 35 78 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 156 252 3 23 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 156 252 4 17 39 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 67 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 252 6 11 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 65 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 252 4 16 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 156 252 3 21 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 156 252 2 31 78 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 61 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 252 12 5 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 252 (Polychromatic418967fa.accept_19_2_4_5_1_3021 59 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 252 2 29 78 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 156 252 3 19 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 156 252 4 14 39 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 252
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 55 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 156 252 6 9 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 156 252 (Polychromatic418967fa.accept_17_2_3_14_1_8043 53 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 252 4 13 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 156 252 3 17 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 156 252 2 25 78 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 252
  (Polychromatic418967fa.accept_17_15_3_14_1_4230 49 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 156 252 12 4 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 156 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 47 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 252 2 23 78 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 156 252 3 15 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 156 252 4 11 39 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 252
  (Polychromatic418967fa.accept_22_21_2_10_1_10682 43 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 156 252 6 7 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 156 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 252 4 10 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 156 252 3 13 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 252 2 19 78 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 252 12 3 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 252 2 17 78 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 156 252 3 11 52 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 252 4 8 39 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 252 6 5 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 156 252 (Polychromatic418967fa.accept_25_4_6_2_1_15364 29 156 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 252 4 7 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 156 252 3 9 52 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 252 2 13 78 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 252
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 156 252 12 2 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 156 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 252 2 11 78 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 156 252 3 7 52 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 156 252 4 5 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 252
  (Polychromatic418967fa.accept_17_2_3_14_1_8043 19 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 252 6 3 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 156 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 252 4 4 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 156 252 3 5 52 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 156 252 2 7 78 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 252
  (Polychromatic418967fa.accept_22_13_2_10_1_15294 13 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 156 252 12 1 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 156 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 156 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 252 2 5 78 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 156 252 3 3 52 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 156 252 4 2 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 156 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 252 6 1 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 156 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 252 4 1 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 252 3 1 52 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 252 2 1 78 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 156 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  155 252 (Eq.refl Bool.true) (allA_succ_of_accept 97 155 252 (accept_3_4 97 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 155 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 96 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 155 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 95 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 155 252 (accept_3_4 94 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 155 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 93 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 155 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 92 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 155 252 (accept_3_4 91 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 155 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 90 155
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 155 252
  (Polychromatic418967fa.accept_23_20_17_22_1_15363 89 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 155 252 (accept_3_4 88 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 155 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 155 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 86 155
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 155 252 (accept_3_4 85 155
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 155 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 84 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 155 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 83 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 155 252 (accept_3_4 82 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 155 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 81 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 155 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 80 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 155 252 (accept_3_4 79 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 155 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 155 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 77 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 252 (accept_3_4 76 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 155 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 75 155
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 155 252
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 74 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 155 252 (accept_3_4 73 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 155 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603 72 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 252 (accept_3_4 70 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 252 (Polychromatic418967fa.accept_13_4_12_5_1_476
  69 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 68 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 155 252 (accept_3_4 67 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 155 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 66 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 155 252 (Polychromatic418967fa.accept_16_1_11_12_1_1774 65 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 252 (accept_3_4 64 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 252
  (Polychromatic418967fa.accept_15_2_5_12_1_369 62 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 252 (accept_3_4 61 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 155 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 60 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 155 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603 59 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 252 (accept_3_4 58 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 155
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 252
  (Polychromatic418967fa.accept_13_4_12_5_1_476 56 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 155 252 (accept_3_4 55 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 155 252 (Polychromatic418967fa.accept_13_2_12_5_1_1602 54 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 155 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 53 155 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 252 (accept_3_4 52 155 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 252
  (Polychromatic418967fa.accept_17_16_2_14_1_6715 50 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 155 252 (accept_3_4 49 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 155 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 252 (accept_3_4 46 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 155 252 (Polychromatic418967fa.accept_19_6_3_5_1_9897 44 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 252 (accept_3_4 43 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 155 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 252 (accept_3_4 40 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 252 (accept_3_4 37 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 155
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 35 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 252 (accept_3_4 34 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 252 (accept_3_4 31 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 155
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 252
  (Polychromatic418967fa.accept_19_10_3_5_1_11346 29 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 155 252 (accept_3_4 28 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 155 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 252 (Polychromatic418967fa.accept_16_10_11_12_1_4835 26
  155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 252 (accept_3_4 25
  155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 24 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 155 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 252 (accept_3_4 22 155 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 155 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 252 (accept_3_4 19 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 252 (accept_3_4 16 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 252
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 252 (accept_3_4 13 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 252 (Polychromatic418967fa.accept_23_12_17_22_1_15290 12 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 252 (Polychromatic418967fa.accept_22_11_1_10_1_15362 11 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 252 (accept_3_4 10 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 252 (Polychromatic418967fa.accept_11_9_1_10_1_920
  9 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 252 (accept_3_4 7 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 252 (Polychromatic418967fa.accept_17_5_2_14_1_4270 5 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 252 (accept_3_4 4 155 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 155 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 252 (accept_3_4 1 155 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  154 252 (Eq.refl Bool.true) (allA_succ_of_gcd 98 154 252 14 7 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 154 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 97 154 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 154 252 2 48 77 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 154 252 (accept_3_5 95
  154 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 154 252 2 47 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 154 252
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 93 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 154 252 2 46 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 154 252 7 13 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 90 154 252 2 45 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 154 252 (accept_3_5 89 154 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 88 154 252 2 44 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 154 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 87 154 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 154 252 2 43 77 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 154 252
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 85 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 154 252 14 6 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 154 252 (accept_3_5 83 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 154 252 2 41 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 154 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 81 154 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 154 252 2 40 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 154 252
  (Polychromatic418967fa.accept_19_3_2_5_1_5679 79 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 154 252 2 39 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 154 252 7 11 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 154 252 2 38 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 154 252 (Polychromatic418967fa.accept_16_11_10_12_1_4832 75 154
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 154 252 2 37 77 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 154 252
  (Polychromatic418967fa.accept_19_16_2_5_1_5681 73 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 154 252 2 36 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 252 (accept_3_5 71 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 252 14 5 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 69 154 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 252 2 34 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 67 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 252 2 33 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 252 (accept_3_5 65 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 252 2 32 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 154 252 7 9 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 154 252 2 31 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 154 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 61 154 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 154 252 2 30 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 154 252 (accept_3_5 59 154 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 154 252 2 29 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 154 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 154 252 14 4 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 154 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 55 154 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 154 252 2 27 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 154 252 (accept_3_5 53 154 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 154 252 2 26 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 154 252
  (Polychromatic418967fa.accept_16_3_10_12_1_4814 51 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 154 252 2 25 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 49 154 252 7 7 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 48 154 252 2 24 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 154 252 (accept_3_5 47 154 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 154 252 2 23 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 154 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 45 154 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 252 2 22 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 252
  (Polychromatic418967fa.accept_16_11_10_12_1_4832 43 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 154 252 14 3 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 154 252 (accept_3_5 41 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 252 2 20 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 154 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 252 2 19 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 252 2 18 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 154 252 7 5 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 154 252 2 17 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 154 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 154 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 252 2 16 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 252
  (Polychromatic418967fa.accept_15_1_4_12_1_2401 31 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 252 2 15 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 252 (accept_3_5 29 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 252 14 2 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 154 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 252 2 13 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 252
  (Polychromatic418967fa.accept_29_25_9_20_1_15361 25 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 154 252 2 12 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 154 252 (accept_3_5 23 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 252 2 11 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 154 252 7 3 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 154 252 2 10 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 154 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 154 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 154 252 2 9 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 154 252 (accept_3_5 17 154 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 154 252 2 8 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 154 252
  (Polychromatic418967fa.accept_23_15_16_22_1_8813 15 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 154 252 14 1 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 154 252 (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 154 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 252 2 6 77 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 252 (accept_3_5 11
  154 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 252 2 5 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 252
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 252 2 4 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 154 252 7 1 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 154 252 2 3 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 252 (accept_3_5 5 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  252 2 2 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 154 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 252 2 1 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1 154 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  153 252 (Eq.refl Bool.true) (allA_succ_of_gcd 99 153 252 9 11 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 153 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 98 153
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 97 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 153 252 3 32 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 153 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 95 153 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 153 252
  (Polychromatic418967fa.accept_19_18_1_5_1_5720 94 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 153 252 3 31 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 153 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 92 153 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 91 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 153 252 9 10 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 153 252 (Polychromatic418967fa.accept_25_14_3_2_1_15206 89 153 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 88 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 153 252 3 29 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 153 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 86 153 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 85 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 153 252 3 28 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 153 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 83 153 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 82 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 153 252 9 9 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 153 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 80 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 252 (Polychromatic418967fa.accept_19_3_1_5_1_8549 79 153
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 153 252 3 26 51 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 153 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 77 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 153 252 (Polychromatic418967fa.accept_23_7_15_22_1_15360 76 153 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 153 252 3 25 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 153 252
  (Polychromatic418967fa.accept_25_24_3_2_1_15359 74 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 153 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 73 153 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 153 252 9 8 17 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 153 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 71 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 153 252 (Polychromatic418967fa.accept_20_10_13_12_1_9726 70 153 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 153 252 3 23 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 153 252
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 68 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 67 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 153 252 3 22 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 153 252 (Polychromatic418967fa.accept_10_5_3_2_1_899
  65 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 252
  (Polychromatic418967fa.accept_22_20_21_10_1_13754 64 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 153 252 9 7 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 153 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 62 153 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 61 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 153 252 3 20 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 153 252 (Polychromatic418967fa.accept_20_19_13_12_1_2476 59 153 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 58 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 153 252 3 19 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 153 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 56 153 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 55 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 153 252 9 6 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 153 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 52 153
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 153 252 3 17 51 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 153 252
  (Polychromatic418967fa.accept_16_2_9_12_1_46 50 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 252 (Polychromatic418967fa.accept_25_24_3_2_1_15359 49 153 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 153 252 3 16 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 153 252
  (Polychromatic418967fa.accept_13_8_10_5_1_977 47 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 252 (Polychromatic418967fa.accept_22_2_21_10_1_9088 46 153 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 153 252 9 5 17 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 153 252
  (Polychromatic418967fa.accept_19_6_1_5_1_5719 44 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 43 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 153 252 3 14 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 252 (Polychromatic418967fa.accept_10_1_3_2_1_220
  41 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 252
  (Polychromatic418967fa.accept_16_8_9_12_1_1737 40 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 252 3 13 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 38 153 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 37 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 153 252 9 4 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 153 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 34 153
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 252 3 11 51 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 32 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 252 3 10 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 29
  153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 252
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 28 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 153 252 9 3 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 153 252 (Polychromatic418967fa.accept_25_1_3_2_1_15358 26 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 153
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 252 3 8 51 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 252
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 22 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 252 3 7 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 252 (Polychromatic418967fa.accept_16_4_9_12_1_4829
  20 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 153 252 9 2 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 153 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 252 (Polychromatic418967fa.accept_19_16_1_5_1_3084 16 153
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 252 3 5 51 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 252
  (Polychromatic418967fa.accept_22_14_21_10_1_13737 14 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 153 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 153 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 252 3 4 51 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 252 (Polychromatic418967fa.accept_20_10_13_12_1_9726 10 153 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 252 9 1 17 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 8
  153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 153 252 3 2 51 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 153 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 153
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 252 3 1 51 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 252
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 2 153 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 153 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 152 252 (Eq.refl Bool.true) (allA_succ_of_gcd 100 152 252 4 25 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 152 252 (Polychromatic418967fa.accept_16_3_8_12_1_2736
  99 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 152 252 2 49 76 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 152 252
  (accept_3_4 97 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 152 252 4 24 38 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 152 252
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 95 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 152 252 2 47 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 152 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 93 152 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 152 252 4 23 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 152 252 (accept_3_4 91 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 152 252 2 45 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 152 252 (Polychromatic418967fa.accept_11_1_9_10_1_184
  89 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 152 252 4 22 38 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 252
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 87 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 152 252 2 43 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 152 252 (accept_3_4 85 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 152 252 4 21 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 152 252 (Polychromatic418967fa.accept_16_3_8_12_1_2736 83 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 252 2 41 76 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 81 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 252 4 20 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 252 (accept_3_4 79 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 252 2 39 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 252 (Polychromatic418967fa.accept_16_13_8_12_1_2723 77 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 252 4 19 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 252
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 75 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 152 252 2 37 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 152 252 (accept_3_4 73 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 252 4 18 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 152 252 (Polychromatic418967fa.accept_16_7_8_12_1_4902 71 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 252 2 35 76 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 252
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 69 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 252 4 17 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 252 (accept_3_4 67 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 252 2 33 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 65 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 252 4 16 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 252
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 252 2 31 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 252 (accept_3_4 61 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 252 4 15 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 252 (Polychromatic418967fa.accept_15_14_2_12_1_2472 59 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 252 2 29 76 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 252
  (Polychromatic418967fa.accept_16_9_8_12_1_979 57 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 252 4 14 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 252 (accept_3_4 55 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 252 2 27 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 53 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 252 4 13 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 252
  (Polychromatic418967fa.accept_15_6_2_12_1_885 51 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 252 2 25 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 252 (accept_3_4 49 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 252 4 12 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 252 (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 252 2 23 76 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 252 4 11 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 252 (accept_3_4 43 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 252 2 21 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 252 4 10 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 252
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 39 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 252 2 19 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 252 (accept_3_4 37 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 252 4 9 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 152 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 152 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 252 2 17 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469
  33 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 252 4 8 38 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 252
  (accept_3_4 31 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 252 2 15 76 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 29 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 152 252 4 7 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 152 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 152 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 252 2 13 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 252 (accept_3_4 25 152 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 252 4 6 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 152
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 252 2 11 76 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 252
  (Polychromatic418967fa.accept_15_6_2_12_1_885 21 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 252 4 5 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 152 252 (accept_3_4 19 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  152 252 2 9 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 152 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 252 4 4 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 252 (Polychromatic418967fa.accept_13_2_9_5_1_959
  15 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 252 2 7 76 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 252
  (accept_3_4 13 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 252 4 3 38 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 252
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 152 252 2 5 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 152 252 (Polychromatic418967fa.accept_16_9_8_12_1_979 9 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 252 4 2 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 252 (accept_3_4 7 152 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 252 2 3 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543
  5 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 252 4 1 38 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 152 252 2 1 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 152 252 (accept_3_4 1 152 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 151 252 (Eq.refl Bool.true) (allA_succ_of_accept 101 151 252 (accept_3_5 101 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 151 252 (Polychromatic418967fa.accept_16_4_7_12_1_2734 100 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 151 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 99 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 151 252 (accept_3_5 98 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 151 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 97 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 151 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 96 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 151 252 (accept_3_5 95 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 151 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 94 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 151 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 93 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 151 252 (accept_3_5 92 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 151 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 91 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 151 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 90 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 151 252 (accept_3_5 89 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 151 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 88 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 252
  (Polychromatic418967fa.accept_25_12_1_2_1_15357 87 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 151 252 (accept_3_5 86 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 151 252 (Polychromatic418967fa.accept_16_5_7_12_1_7206 85 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 151 252 (Polychromatic418967fa.accept_16_4_7_12_1_2734 84 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 252 (accept_3_5 83 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 151 252
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 82 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 151 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 81 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 151 252 (accept_3_5 80 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 151 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 79 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 151 252
  (Polychromatic418967fa.accept_19_2_18_5_1_11293 78 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 151 252 (accept_3_5 77 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 151 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 76 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 151 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 252 (accept_3_5 74 151 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 151 252 (Polychromatic418967fa.accept_10_3_1_2_1_521
  73 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 252
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 72 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 151 252 (accept_3_5 71 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 151 252 (Polychromatic418967fa.accept_19_13_18_5_1_8619 70 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 151 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 69 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 252 (accept_3_5 68 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 151 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 66 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 252 (accept_3_5 65 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 64 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 252 (accept_3_5 62 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 252 (Polychromatic418967fa.accept_19_4_18_5_1_929 61 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 252
  (Polychromatic418967fa.accept_23_14_13_22_1_15356 60 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 151 252 (accept_3_5 59 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 151 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 58 151 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 252
  (Polychromatic418967fa.accept_17_6_15_14_1_8027 57 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 151 252 (accept_3_5 56 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 151 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 55 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 252 (Polychromatic418967fa.accept_17_3_15_14_1_4219 54 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 252 (accept_3_5 53 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 252
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 52 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 151 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 252 (accept_3_5 50 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 151 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 252
  (Polychromatic418967fa.accept_19_10_18_5_1_5673 48 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 151 252 (accept_3_5 47 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 151 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 252 (Polychromatic418967fa.accept_22_1_19_10_1_15355 45
  151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 252 (accept_3_5 44
  151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 151 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 252 (accept_3_5 41 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 151 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 40 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 39 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 252 (accept_3_5 38 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 252 (Polychromatic418967fa.accept_16_5_7_12_1_7206 37 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 252 (accept_3_5 35 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 34 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 33 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 252 (accept_3_5 32 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 252 (Polychromatic418967fa.accept_22_8_19_10_1_12159 30 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 252 (accept_3_5 29 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 252 (accept_3_5 26 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 25 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 252 (Polychromatic418967fa.accept_16_8_7_12_1_7207 24 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 252 (accept_3_5 23 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 252 (Polychromatic418967fa.accept_26_22_21_18_1_15354 22
  151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 252
  (Polychromatic418967fa.accept_16_5_7_12_1_7206 21 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 252 (accept_3_5 20 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 252 (Polychromatic418967fa.accept_16_2_7_12_1_3793 18 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 252 (accept_3_5 17 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 252
  (Polychromatic418967fa.accept_25_15_1_2_1_15353 15 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 151 252 (accept_3_5 14 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 151 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 252 (accept_3_5 11 151
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 252
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 151 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 252 (accept_3_5 8 151 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 151 252 (Polychromatic418967fa.accept_22_7_19_10_1_15352 7 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 252 (accept_3_5 5 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 151 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 151 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 252 (accept_3_5 2 151 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 151 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 150 252 (Eq.refl Bool.true) (allA_succ_of_gcd 102 150 252 6 17 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 150 252
  (Polychromatic418967fa.accept_23_9_12_22_1_13706 101 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 150 252 2 50 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 99 150 252 3 33 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 150 252 2 49 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 150 252 (Polychromatic418967fa.accept_19_2_17_5_1_5643
  97 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 252 6 16 25 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 150 252
  (Polychromatic418967fa.accept_20_15_10_12_1_13874 95 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 94 150 252 2 47 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 93 150 252 3 31 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 150 252 2 46 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 150 252 (Polychromatic418967fa.accept_11_3_7_10_1_180
  91 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 150 252 6 15 25 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 150 252
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 89 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 150 252 2 44 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 150 252 3 29 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 150 252 2 43 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 150 252 (Polychromatic418967fa.accept_20_5_10_12_1_8200 85 150
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 150 252 6 14 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 252
  (Polychromatic418967fa.accept_19_7_17_5_1_3081 83 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 150 252 2 41 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 150 252 3 27 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 150 252 2 40 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 252 (Polychromatic418967fa.accept_19_3_17_5_1_955 79 150
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 150 252 6 13 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 150 252
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 77 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 150 252 2 38 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 150 252 3 25 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 252 2 37 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 252 (Polychromatic418967fa.accept_20_13_10_12_1_2462 73 150
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 252 6 12 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 252
  (Polychromatic418967fa.accept_19_14_17_5_1_15232 71 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 150 252 2 35 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 150 252 3 23 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 150 252 2 34 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189
  67 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 252 6 11 25 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 150 252
  (Polychromatic418967fa.accept_20_5_10_12_1_8200 65 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 150 252 2 32 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 63 150 252 3 21 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 150 252 2 31 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 252
  (Polychromatic418967fa.accept_22_17_18_10_1_5783 61 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 150 252 6 10 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 150 252 (Polychromatic418967fa.accept_19_2_17_5_1_5643 59 150 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 252 2 29 75 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 150 252 3 19 50 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 150 252 2 28 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 252
  (Polychromatic418967fa.accept_20_15_10_12_1_13874 55 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 150 252 6 9 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 150 252 (Polychromatic418967fa.accept_19_15_17_5_1_3052 53 150 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 252 2 26 75 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 150 252 3 17 50 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 150 252 2 25 75
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 252
  (Polychromatic418967fa.accept_19_11_17_5_1_8609 49 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 150 252 6 8 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 150 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 47 150 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 252 2 23 75 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 150 252 3 15 50 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 252 2 22 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 252
  (Polychromatic418967fa.accept_20_3_10_12_1_11106 43 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 150 252 6 7 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 150 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 41 150 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 252 2 20 75 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 150 252 3 13 50 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 252 2 19 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 252
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 252 6 6 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 150 252 (Polychromatic418967fa.accept_20_15_10_12_1_13874 35 150 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 252 2 17 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 150 252 3 11 50 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 252 2 16 75 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 252
  (Polychromatic418967fa.accept_19_12_17_5_1_5702 31 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 150 252 6 5 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 150 252 (Polychromatic418967fa.accept_23_6_12_22_1_15351 29 150 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 252 2 14 75 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 150 252 3 9 50 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 150 252 2 13 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 252
  (Polychromatic418967fa.accept_11_3_7_10_1_180 25 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 252 6 4 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 150 252 (Polychromatic418967fa.accept_20_3_10_12_1_11106 23 150 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 252 2 11 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 150 252 3 7 50 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 150 252 2 10 75 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 252
  (Polychromatic418967fa.accept_24_19_6_12_1_15282 19 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 150 252 6 3 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 150 252 (Polychromatic418967fa.accept_22_17_18_10_1_5783 17 150 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 252 2 8 75 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 252 3 5 50 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 252 2 7 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 252
  (Polychromatic418967fa.accept_20_13_10_12_1_2462 13 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 150 252 6 2 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 150 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 150 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 252 2 5 75 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 252 3 3 50 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 252 2 4 75 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 252
  (Polychromatic418967fa.accept_19_7_17_5_1_3081 7 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 252 6 1 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 252 (Polychromatic418967fa.accept_20_5_10_12_1_8200 5 150 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 252 2 2 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 252 3 1 50 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 252 2 1 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 252 (Polychromatic418967fa.accept_24_1_6_12_1_8449
  1 150 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 149 252 (Eq.refl Bool.true) (allA_succ_of_accept 103 149 252 (accept_3_4 103 149 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 149 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 102 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 149 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 101 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 149 252 (accept_3_4 100 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 149 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 99 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 149 252 (Polychromatic418967fa.accept_19_3_16_5_1_7098 98 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 149 252 (accept_3_4 97 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 149 252 (Polychromatic418967fa.accept_19_1_16_5_1_5671 96 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 149 252
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 95 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 149 252 (accept_3_4 94 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 149 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 93 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 149 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 92 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 149 252 (accept_3_4 91 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 149 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 90 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 149 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 89 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 149 252 (accept_3_4 88 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 149 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 87 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 149 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 86 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 252 (accept_3_4 85 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 84 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 252
  (Polychromatic418967fa.accept_20_3_9_12_1_6671 83 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 149 252 (accept_3_4 82 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 149 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 149 252 (Polychromatic418967fa.accept_24_8_5_12_1_15350 80 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 252 (accept_3_4 79 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 252 (Polychromatic418967fa.accept_17_10_13_14_1_3094 78
  149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 77 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 149 252 (accept_3_4 76 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 149 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 75 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 149 252 (Polychromatic418967fa.accept_16_10_5_12_1_4925 74 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 252 (accept_3_4 73 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 252 (Polychromatic418967fa.accept_16_8_5_12_1_3812 72 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 71 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 149 252 (accept_3_4 70 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 149 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 69 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 149 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 68 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 252 (accept_3_4 67 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 66 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 252 (accept_3_4 64 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 62 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 252 (accept_3_4 61 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 252
  (Polychromatic418967fa.accept_19_2_16_5_1_9932 59 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 252 (accept_3_4 58 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 56 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 252 (accept_3_4 55 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 54 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 252
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 53 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 149 252 (accept_3_4 52 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 149 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 149 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 50 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 252 (accept_3_4 49 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 252 (Polychromatic418967fa.accept_19_10_16_5_1_8562 48 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 252 (accept_3_4 46 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 252 (Polychromatic418967fa.accept_27_18_14_9_1_15349 45 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 252 (Polychromatic418967fa.accept_17_10_13_14_1_3094 44 149 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 252 (accept_3_4 43 149 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336
  42 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 252 (accept_3_4 40 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 252 (accept_3_4 37 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 252
  (Polychromatic418967fa.accept_17_1_13_14_1_478 35 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 252 (accept_3_4 34 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 252 (Polychromatic418967fa.accept_15_2_14_12_1_2453 32 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 252 (accept_3_4 31 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 30 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 252
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 252 (accept_3_4 28 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 252 (accept_3_4 25 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 252
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 252 (accept_3_4 22 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 252 (Polychromatic418967fa.accept_16_4_5_12_1_2749 20 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 252 (accept_3_4 19 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 252 (Polychromatic418967fa.accept_17_1_13_14_1_478 18 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 252 (accept_3_4 16 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 252 (Polychromatic418967fa.accept_22_15_17_10_1_10687 15 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 252 (accept_3_4 13 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 252 (accept_3_4 10 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 252 (Polychromatic418967fa.accept_16_8_5_12_1_3812 8 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 252 (accept_3_4 7 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 252 (Polychromatic418967fa.accept_22_6_17_10_1_12202 6 149
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 252 (accept_3_4 4 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 149 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 252 (Polychromatic418967fa.accept_15_2_14_12_1_2453 2 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 252 (accept_3_4 1 149 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 149
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 148 252 (Eq.refl Bool.true) (allA_succ_of_gcd 104 148 252 4 26 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 148 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 103 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 148 252 2 51 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 148 252 (accept_3_5 101 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 148 252 4 25 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 148 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 99 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 148 252 2 49 74 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 148 252
  (Polychromatic418967fa.accept_16_1_4_12_1_376 97 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 148 252 4 24 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 148 252 (accept_3_5 95 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 148 252 2 47 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 148 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 93 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 148 252 4 23 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 148 252
  (Polychromatic418967fa.accept_15_1_13_12_1_347 91 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 148 252 2 45 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 148 252 (accept_3_5 89 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 148 252 4 22 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 148 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 87 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 148 252 2 43 74 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 148 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 85 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 148 252 4 21 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 148 252 (accept_3_5 83 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 148 252 2 41 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 148 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 81 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 148 252 4 20 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 148 252
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 79 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 148 252 2 39 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 148 252 (accept_3_5 77 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 252 4 19 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 75 148 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 252 2 37 74 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 252
  (Polychromatic418967fa.accept_16_9_4_12_1_4896 73 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 252 4 18 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 252 (accept_3_5 71 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 252 2 35 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 252 (Polychromatic418967fa.accept_16_5_4_12_1_3800 69 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 252 4 17 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 252
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 67 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 252 2 33 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 252 (accept_3_5 65 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 252 4 16 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 63 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 252 2 31 74 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 61 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 252 4 15 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 252 (accept_3_5 59 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 252 2 29 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 252 (Polychromatic418967fa.accept_16_9_4_12_1_4896 57 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 252 4 14 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 55 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 252 2 27 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 252 (accept_3_5 53 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 252 4 13 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 51 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 252 2 25 74 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 252
  (Polychromatic418967fa.accept_16_1_4_12_1_376 49 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 252 4 12 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 252 (accept_3_5 47 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 252 2 23 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 148 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 252 4 11 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 252
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 43 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 148 252 2 21 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 148 252 (accept_3_5 41 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 252 4 10 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 252 2 19 74 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 37 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 252 4 9 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 252 (accept_3_5 35 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  148 252 2 17 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 148 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 33 148 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 252 4 8 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 252 (Polychromatic418967fa.accept_15_1_13_12_1_347
  31 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 148 252 2 15 74 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 148 252
  (accept_3_5 29 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 148 252 4 7 37 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 148 252
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 27 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 148 252 2 13 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 148 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 148 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 148 252 4 6 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 148 252 (accept_3_5 23 148 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 148 252 2 11 74 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 148 252
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 148 252 4 5 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 148 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 19 148 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 148 252 2 9 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 148 252 (accept_3_5 17 148 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 148 252 4 4 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 148 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 148 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 252 2 7 74 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 252
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 148 252 4 3 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 148 252 (accept_3_5 11 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 252 2 5 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 252 (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 148 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 252 4 2 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806
  7 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 252 2 3 74 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 252 (accept_3_5 5
  148 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 252 4 1 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 148 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 3 148 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 148 252 2 1 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 148 252 (Polychromatic418967fa.accept_15_1_13_12_1_347 1 148 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 148
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 147 252 (Eq.refl Bool.true) (allA_succ_of_gcd 105 147 252 21 5 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 147 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 104 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 147 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 103 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 147 252 3 34 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 147 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 101 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 147 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 100 147 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 147 252 3 33 49 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 147 252 7 14 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 147 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 97 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 147 252 3 32 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 147 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 95 147 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 252 (Polychromatic418967fa.accept_10_4_7_2_1_211
  94 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 147 252 3 31 49 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 147 252
  (Polychromatic418967fa.accept_13_1_4_5_1_113 92 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 91 147 252 7 13 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 90 147 252 3 30 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 147 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 89 147 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 88 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 147 252 3 29 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 147 252 (Polychromatic418967fa.accept_19_10_14_5_1_3079 86 147 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 85 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 147 252 21 4 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 147 252 (Polychromatic418967fa.accept_22_17_15_10_1_15283 83 147 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 252 (Polychromatic418967fa.accept_11_5_4_10_1_524
  82 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 147 252 3 27 49 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 147 252
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 80 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 147 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 79 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 147 252 3 26 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 147 252 7 11 21 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 147 252
  (Polychromatic418967fa.accept_17_8_11_14_1_6770 76 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 147 252 3 25 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 147 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 147 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 252
  (Polychromatic418967fa.accept_16_9_3_12_1_1802 73 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 147 252 3 24 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 147 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 147 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 147 252 7 10 21 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 147 252 3 23 49 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 147 252
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 68 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 147 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 67 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 147 252 3 22 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 147 252 (Polychromatic418967fa.accept_10_5_7_2_1_516
  65 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 64 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 147 252 21 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 147 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 62 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 61 147
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 147 252 3 20 49 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 147 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 59 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 58 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 147 252 3 19 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 147 252 7 8 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 147 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 55
  147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 147 252 3 18 49 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 147 252
  (Polychromatic418967fa.accept_13_1_4_5_1_113 53 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 52 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 147 252 3 17 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 147 252
  (Polychromatic418967fa.accept_17_16_11_14_1_4213 50 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 147 252 7 7 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 48 147 252 3 16 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 147 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 147 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 252
  (Polychromatic418967fa.accept_17_12_11_14_1_3120 46 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 147 252 3 15 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 147 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 147 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 252
  (Polychromatic418967fa.accept_25_18_22_2_1_15348 43 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 147 252 21 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 147 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 41 147 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 252
  (Polychromatic418967fa.accept_13_1_4_5_1_113 40 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 147 252 3 13 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 147 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 38 147 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 252
  (Polychromatic418967fa.accept_17_3_11_14_1_2071 37 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 147 252 3 12 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 147 252 7 5 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 147 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 147 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 147 252 3 11 49 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 147 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 32 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 252 3 10 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 252 (Polychromatic418967fa.accept_10_9_7_2_1_887
  29 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 147 252 7 4 21 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 147 252 3 9 49 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 252
  (Polychromatic418967fa.accept_16_10_3_12_1_1758 26 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 147 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 147 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 252 3 8 49 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 22 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 252 21 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892
  20 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 19 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 147 252 3 6 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 147 252 (Polychromatic418967fa.accept_19_17_14_5_1_8561 17 147 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 252 (Polychromatic418967fa.accept_11_5_4_10_1_524
  16 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 252 3 5 49 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 147 252 7 2 21 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 147 252
  (Polychromatic418967fa.accept_19_13_14_5_1_8545 13 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 147 252 3 4 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 147 252 (Polychromatic418967fa.accept_19_11_14_5_1_5629 11 147 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 147 252 3 3 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 252 (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147 252 7 1 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 147 252 3 2 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 147 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 147 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 252 3 1 49 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 147 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 147 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 146 252 (Eq.refl Bool.true) (allA_succ_of_gcd 106 146 252 2 53 73 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 146 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 105 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 146 252 2 52 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 146 252 (accept_3_4 103 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 146 252 2 51 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 146 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 101 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 146 252 2 50 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 146 252
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 99 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 146 252 2 49 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 146 252 (accept_3_4 97 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 146 252 2 48 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 146 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 95 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 146 252 2 47 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 146 252
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 93 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 146 252 2 46 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 146 252 (accept_3_4 91 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 146 252 2 45 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 146 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 89 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 252 2 44 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 252
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 87 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 252 2 43 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 252 (accept_3_4 85 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 252 2 42 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 252 (Polychromatic418967fa.accept_15_8_11_12_1_1626 83 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 252 2 41 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 252 2 40 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 252 (accept_3_4 79 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 252 2 39 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 252 (Polychromatic418967fa.accept_20_17_6_12_1_8185 77 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 252 2 38 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 252
  (Polychromatic418967fa.accept_17_7_10_14_1_8022 75 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 146 252 2 37 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 146 252 (accept_3_4 73 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 252 2 36 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 146 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 252 2 35 73 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 252
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 69 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 146 252 2 34 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 146 252 (accept_3_4 67 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 252 2 33 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 252 (Polychromatic418967fa.accept_16_1_2_12_1_1757 65 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 252 2 32 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 252
  (Polychromatic418967fa.accept_13_11_3_5_1_982 63 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 146 252 2 31 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 146 252 (accept_3_4 61 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 252 2 30 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 252 (Polychromatic418967fa.accept_15_14_11_12_1_4440 59 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 252 2 29 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 252
  (Polychromatic418967fa.accept_16_9_2_12_1_1800 57 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 252 2 28 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 252 (accept_3_4 55 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 252 2 27 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 53 146 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 252 2 26 73 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 252 2 25 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 252 (accept_3_4 49 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 252 2 24 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 47 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 252 2 23 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 252
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 252 2 22 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 252 (accept_3_4 43 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 252 2 21 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 146 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 252 2 20 73 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 252
  (Polychromatic418967fa.accept_16_7_2_12_1_1754 39 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 252 2 19 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 252 (accept_3_4 37 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 252 2 18 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 252 2 17 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 252
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 33 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 252 2 16 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 252 (accept_3_4 31 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 252 2 15 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 252 2 14 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 252 2 13 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 252 (accept_3_4 25 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 252 2 12 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 252 (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 252 2 11 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 252 2 10 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 252 (accept_3_4 19 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 252 2 9 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 252 (Polychromatic418967fa.accept_16_1_2_12_1_1757 17 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 252 2 8 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 252
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 252 2 7 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 252 (accept_3_4 13 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 252 2 6 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 146 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 252 2 5 73 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 252
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 252 2 4 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 252 (accept_3_4 7 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  252 2 3 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 252 (Polychromatic418967fa.accept_17_5_10_14_1_2083 5 146 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 252 2 2 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 252 (Polychromatic418967fa.accept_27_3_11_9_1_13406 3 146 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 252 2 1 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 252 (accept_3_4 1 146 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 145 252 (Eq.refl Bool.true) (allA_succ_of_accept 107 145 252 (accept_3_5 107 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 145 252 (Polychromatic418967fa.accept_17_4_9_14_1_5406 106
  145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 145 252
  (Polychromatic418967fa.accept_25_5_20_2_1_15347 105 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 145 252 (accept_3_5 104 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 145 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 103 145 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 145 252 (Polychromatic418967fa.accept_19_7_12_5_1_7123 102
  145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 145 252 (accept_3_5 101
  145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 145 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 100 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 145 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 99 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 145 252 (accept_3_5 98 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 145 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 97 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 145 252
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 96 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 145 252 (accept_3_5 95 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 145 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 94 145 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 145 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 93 145 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 145 252 (accept_3_5 92 145 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 145 252
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 91 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 145 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 90 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 145 252 (accept_3_5 89 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 88 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 87 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 145 252 (accept_3_5 86 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 145 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 85 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 145 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 84 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 252 (accept_3_5 83 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 82 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 252
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 81 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 145 252 (accept_3_5 80 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 145 252 (Polychromatic418967fa.accept_25_4_20_2_1_11798 79 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 145 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 252 (accept_3_5 77 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 252 (Polychromatic418967fa.accept_24_4_1_12_1_4887 76 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 252
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 75 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 145 252 (accept_3_5 74 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 145 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 73 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 145 252 (Polychromatic418967fa.accept_13_7_2_5_1_2344 72 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 252 (accept_3_5 71 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 145 252 (Polychromatic418967fa.accept_19_13_12_5_1_9943 70 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 252 (accept_3_5 68 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 67 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 66 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 252 (accept_3_5 65 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 64 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 63 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 252 (accept_3_5 62 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 145 252 (Polychromatic418967fa.accept_26_8_15_18_1_15346 60 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 252 (accept_3_5 59 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 58 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 57 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 252 (accept_3_5 56 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 55 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 145 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 54 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 252 (accept_3_5 53 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 252
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 51 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 252 (accept_3_5 50 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 49 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 252 (accept_3_5 47 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 252 (Polychromatic418967fa.accept_13_7_2_5_1_2344 46 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 252 (accept_3_5 44 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 252 (accept_3_5 41 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 252 (Polychromatic418967fa.accept_16_8_1_12_1_984 40 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 145 252 (accept_3_5 38 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 145 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 145 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 252 (accept_3_5 35 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 145 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 145 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 252 (accept_3_5 32 145 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 145 252 (Polychromatic418967fa.accept_22_9_13_10_1_15214 31 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 252
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 145 252 (accept_3_5 29 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 145 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 252 (accept_3_5 26 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 25 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 145 252 (accept_3_5 23 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 145 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 22 145 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 145 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 252 (accept_3_5 20 145 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 252
  (Polychromatic418967fa.accept_22_19_13_10_1_12177 19 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 252 (accept_3_5 17 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 252
  (Polychromatic418967fa.accept_19_15_12_5_1_8544 15 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 145 252 (accept_3_5 14 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 145 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 145 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 252 (accept_3_5 11 145
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 252
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 145 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 145 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 252 (accept_3_5 8 145 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 145 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 145 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 252
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 252 (accept_3_5 5 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 145 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 145 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 252 (accept_3_5 2 145 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 145 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 144 252 (Eq.refl Bool.true) (allA_succ_of_gcd 108 144 252 36 3 4 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 144 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 107 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 144 252 2 53 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 144 252 3 35 48 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 144 252 4 26 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 144 252 (Polychromatic418967fa.accept_13_12_1_5_1_1650 103 144
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 144 252 6 17 24 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 144 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 101 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 144 252 4 25 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 144 252 9 11 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 144 252 2 49 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 144 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 97 144 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 144 252 12 8 12 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 252
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 95 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 144 252 2 47 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 144 252 3 31 48 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 144 252 4 23 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 144 252 (Polychromatic418967fa.accept_17_6_8_14_1_6706 91 144
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 144 252 18 5 8 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 144 252
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 89 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 144 252 4 22 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 144 252 3 29 48 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 144 252 2 43 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 252
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 85 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 144 252 12 7 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 144 252 (Polychromatic418967fa.accept_25_8_19_2_1_15264 83 144 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 252 2 41 72 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 144 252 9 9 16 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 144 252 4 20 36 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 79 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 252 6 13 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 144 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 252 4 19 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 144 252 3 25 48 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 144 252 2 37 72 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 252
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 73 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 252 36 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 144 252 (Polychromatic418967fa.accept_13_6_1_5_1_3988 71 144 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 252 2 35 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 144 252 3 23 48 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 144 252 4 17 36 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 67 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 252 6 11 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 65 144 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 252 4 16 36 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 144 252 9 7 16 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 144 252 2 31 72 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 252
  (Polychromatic418967fa.accept_13_9_1_5_1_964 61 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 252 12 5 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 144 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 252 2 29 72 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 144 252 3 19 48 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 144 252 4 14 36 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 252
  (Polychromatic418967fa.accept_13_3_1_5_1_499 55 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 252 18 3 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 144 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 53 144 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 252 4 13 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 144 252 3 17 48 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 144 252 2 25 72 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 252
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 49 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 252 12 4 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 144 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 252 2 23 72 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 144 252 9 5 16 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 252 4 11 36 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 252
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 43 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 252 6 7 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 144 252 (Polychromatic418967fa.accept_17_7_8_14_1_6720 41 144 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 252 4 10 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 144 252 3 13 48 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 252 2 19 72 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 252 36 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 35 144 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 252 2 17 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 144 252 3 11 48 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 252 4 8 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 31 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 252 6 5 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 144 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 29 144 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 252 4 7 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 144 252 9 3 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 144 252 2 13 72 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 252 12 2 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 252 (Polychromatic418967fa.accept_17_6_8_14_1_6706 23 144 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 252 2 11 72 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 252 3 7 48 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 252 4 5 36 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 252 18 1 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 144 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 252 4 4 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 144 252 3 5 48 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 252 2 7 72 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 13 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 252 12 1 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 252 (Polychromatic418967fa.accept_17_11_8_14_1_8084 11 144 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 252 2 5 72 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 144 252 9 1 16 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 144 252 4 2 36 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 144 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 252 6 1 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 144 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 252 4 1 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 252 3 1 48 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 252 2 1 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 252 (Polychromatic418967fa.accept_23_1_6_22_1_15345 1 144
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 143 252 (Eq.refl Bool.true) (allA_succ_of_accept 109 143 252 (accept_3_4 109 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 143 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 108 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 143 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 107 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 143 252 (accept_3_4 106 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 143 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 105 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 143 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 104 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 143 252 (accept_3_4 103 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 143 252 (Polychromatic418967fa.accept_19_7_10_5_1_3090 102
  143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 143 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 101 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 143 252 (accept_3_4 100 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 143 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 99 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 143 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744 98 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 143 252 (accept_3_4 97 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 143 252 (Polychromatic418967fa.accept_22_8_11_10_1_5822 96 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 143 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 95 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 143 252 (accept_3_4 94 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 143 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 93 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 143 252 (Polychromatic418967fa.accept_19_16_10_5_1_7106 92 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 252 (accept_3_4 91 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 252 (Polychromatic418967fa.accept_19_14_10_5_1_3073 90 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 252
  (Polychromatic418967fa.accept_17_4_7_14_1_10583 89 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 143 252 (accept_3_4 88 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 143 252 (Polychromatic418967fa.accept_19_11_10_5_1_5662 87 143 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 143 252
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 86 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 143 252 (accept_3_4 85 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 143 252 (Polychromatic418967fa.accept_16_4_15_12_1_1745 84 143 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 83
  143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 143 252 (accept_3_4 82
  143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 143 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 81 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 143 252 (Polychromatic418967fa.accept_15_5_8_12_1_2435 80 143 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 252 (accept_3_4 79 143 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 143 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 78 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 252
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 77 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 143 252 (accept_3_4 76 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 143 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 143 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 252 (Polychromatic418967fa.accept_17_6_7_14_1_6704 74 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 252 (accept_3_4 73 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 252
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 72 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 143 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 71 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 252 (accept_3_4 70 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 252 (Polychromatic418967fa.accept_20_9_3_12_1_6627 69 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 252
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 68 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 143 252 (accept_3_4 67 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 143 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744 66 143 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 252 (Polychromatic418967fa.accept_10_5_3_2_1_899
  65 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 252 (accept_3_4 64
  143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 252
  (Polychromatic418967fa.accept_15_3_8_12_1_900 63 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 143 252 (Polychromatic418967fa.accept_22_18_11_10_1_12153 62 143 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 252 (accept_3_4 61 143 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 252 (Polychromatic418967fa.accept_19_3_10_5_1_4314 60 143 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 252 (accept_3_4 58 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 252 (Polychromatic418967fa.accept_17_6_7_14_1_6704 57 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 252 (Polychromatic418967fa.accept_15_11_8_12_1_4437 56 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 252 (accept_3_4 55 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 252 (Polychromatic418967fa.accept_19_16_10_5_1_7106 54 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 252
  (Polychromatic418967fa.accept_19_15_10_5_1_5637 53 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 143 252 (accept_3_4 52 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 143 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 143 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 252 (Polychromatic418967fa.accept_15_5_8_12_1_2435 50 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 252 (accept_3_4 49 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 252
  (Polychromatic418967fa.accept_15_3_8_12_1_900 48 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 143 252 (Polychromatic418967fa.accept_22_3_11_10_1_15344 47 143 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 252 (accept_3_4 46 143 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 252
  (Polychromatic418967fa.accept_17_10_7_14_1_4244 44 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 143 252 (accept_3_4 43 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 143 252 (Polychromatic418967fa.accept_17_8_7_14_1_11730 42 143 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 252 (Polychromatic418967fa.accept_10_1_3_2_1_220
  41 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 252 (accept_3_4 40
  143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 252
  (Polychromatic418967fa.accept_27_12_8_9_1_15343 39 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 252 (Polychromatic418967fa.accept_17_4_7_14_1_10583 38 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 252 (accept_3_4 37 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 252 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 252 (accept_3_4 34 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 252 (Polychromatic418967fa.accept_19_13_10_5_1_11329 32 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 252 (accept_3_4 31 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 252 (Polychromatic418967fa.accept_19_11_10_5_1_5662 30 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 252
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 29 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 143 252 (accept_3_4 28 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 143 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 143 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 252 (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 252 (accept_3_4 25 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 252
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 252 (Polychromatic418967fa.accept_17_6_7_14_1_6704 23 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 252 (accept_3_4 22 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 252
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 252 (accept_3_4 19 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 252 (Polychromatic418967fa.accept_23_17_5_22_1_12028 17 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 252 (accept_3_4 16 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 143
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 252
  (Polychromatic418967fa.accept_19_14_10_5_1_3073 14 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 143 252 (accept_3_4 13 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 143 252 (Polychromatic418967fa.accept_22_12_11_10_1_15342 12 143 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 11
  143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 252 (accept_3_4 10
  143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 252
  (Polychromatic418967fa.accept_20_9_3_12_1_6627 9 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 143 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 143 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 252 (accept_3_4 7 143 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 143 252 (Polychromatic418967fa.accept_17_6_7_14_1_6704 6 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 252 (accept_3_4 4 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 143 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744 2 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 252 (accept_3_4 1 143 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 143
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_252_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


