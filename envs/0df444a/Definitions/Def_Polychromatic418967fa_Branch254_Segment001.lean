-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch254_Segment001
-- name    : Polychromatic418967fa_Branch254_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:44:39.210816+00:00
-- url     : https://prove2.me/theorems/787208f4-9112-4546-8f93-6acac74a4265
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch254_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_254_segment_001 : allB 206 254 :=
  allB_succ' 50 205 254 (Eq.refl Bool.true) (allA_of_3_0 50 205 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  51 204 254 (Eq.refl Bool.true) (allA_succ_of_gcd 50 204 254 2 25 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 204 254 (accept_3_2 49 204 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 204 254 2 24 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 204 254 (Polychromatic418967fa.accept_13_8_9_7_1_530 47 204 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 204 254 2 23 102 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 204 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 204 254 2 22 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 204 254 (accept_3_2 43 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 204 254 2 21 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 204 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 204 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 204 254 2 20 102 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 204 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 204 254 2 19 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 204 254 (accept_3_2 37 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 254 2 18 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 204 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 204 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 254 2 17 102 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 204 254
  (Polychromatic418967fa.accept_20_13_4_14_1_1457 33 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 204 254 2 16 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 204 254 (accept_3_2 31 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 204 254 2 15 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 204 254 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 204 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 254 2 14 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 204 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 204 254 2 13 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 204 254 (accept_3_2 25 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 204 254 2 12 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 204 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 204 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 254 2 11 102 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 204 254 2 10 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 204 254 (accept_3_2 19 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 254 2 9 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 204 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 204 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 254 2 8 102 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 254
  (Polychromatic418967fa.accept_13_2_9_7_1_164 15 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 204 254 2 7 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 204 254 (accept_3_2 13 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 254 2 6 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 204 254 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 204 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 254 2 5 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 204 254
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 204 254 2 4 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 204 254 (accept_3_2 7 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 254 2 3 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 204 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 204 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 254 2 2 102 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 254 2 1 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 254 (accept_3_2 1 204 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  254))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 203 254 (Eq.refl Bool.true) (allA_succ_of_accept
  51 203 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 203 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 203 254 (accept_3_2 49 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 203 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 203 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 254
  (Polychromatic418967fa.accept_10_7_3_4_1_978 47 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 203 254 (accept_3_2 46 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 203 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 203 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 203 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 254 (accept_3_2 43 203 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 203 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 203 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 203 254 (accept_3_2 40 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 203 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 203 254 (Polychromatic418967fa.accept_13_12_8_7_1_2526 38 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 254 (accept_3_2 37 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 254 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 203
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 203 254 (accept_3_2 34 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 254 (accept_3_2 31 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 203 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 254 (accept_3_2 28 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 203 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 254 (accept_3_2 25 203 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 254
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 23 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 254 (accept_3_2 22 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 254 (accept_3_2 19 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 254 (Polychromatic418967fa.accept_22_18_5_12_1_4337 18 203
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 254 (accept_3_2 16 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 254 (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 254 (accept_3_2 13 203 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 203 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 254
  (Polychromatic418967fa.accept_19_11_13_7_1_5862 11 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 203 254 (accept_3_2 10 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 203 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 203 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 203 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 254 (accept_3_2 7 203 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 254 (accept_3_2 4 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 254 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2 203 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 254 (accept_3_2 1 203 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 254)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 202 254
  (Eq.refl Bool.true) (allA_of_3_0 53 202 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 201 254 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 201 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 254 (accept_3_2 52 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 201 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 201 254 (accept_3_2 49 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 201 254 (Polychromatic418967fa.accept_13_9_6_7_1_551 48 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 201 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 254 (accept_3_2 46 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 201 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 201 254 (accept_3_2 43 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 201 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 201 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 254 (accept_3_2 40 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 201 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 201 254 (accept_3_2 37 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 201 254 (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 201 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 254 (accept_3_2 34 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 201 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 201 254 (accept_3_2 31 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 201 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 201 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 254 (accept_3_2 28 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 201 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 254 (accept_3_2 25 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 201 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 201 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 254 (accept_3_2 22 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 254 (Polychromatic418967fa.accept_14_7_5_2_1_2473 21 201 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 254
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 254 (accept_3_2 19 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 254 (accept_3_2 16 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 201 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 254 (accept_3_2 13 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 254 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 254 (accept_3_2 10 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 254 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 201 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 254 (accept_3_2 7 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 254 (accept_3_2 4 201 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 201 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 254
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 254 (accept_3_2 1 201 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 200 254 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 200 254 2 27 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 200 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 200 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 200 254 2 26 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 200 254 (Polychromatic418967fa.accept_13_12_5_7_1_1696
  51 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 200 254 2 25 100 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 200 254
  (accept_3_2 49 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 200 254 2 24 100 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 200 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 200 254 2 23 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 200 254 (Polychromatic418967fa.accept_22_1_2_12_1_15532 45 200 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 200 254 2 22 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 200 254 (accept_3_2 43 200 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 200 254 2 21 100 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 200 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 200 254 2 20 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 200 254 (Polychromatic418967fa.accept_15_9_5_14_1_973 39 200 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 200 254 2 19 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 200 254 (accept_3_2 37 200 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 200 254 2 18 100 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 200 254
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 200 254 2 17 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 200 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 200 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 200 254 2 16 100 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 200 254 (accept_3_2 31 200 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 200 254 2 15 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 200 254 (Polychromatic418967fa.accept_12_5_8_2_1_309
  29 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 254 2 14 100 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 200 254 2 13 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 200 254 (accept_3_2 25 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 200 254 2 12 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 200 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 200 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 254 2 11 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 254
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 200 254 2 10 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 200 254 (accept_3_2 19 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 200 254 2 9 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 200 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 200 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 254 2 8 100 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 200 254
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 200 254 2 7 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 200 254 (accept_3_2 13 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 200 254 2 6 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 200 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 200 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 254 2 5 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 254
  (Polychromatic418967fa.accept_14_9_4_2_1_983 9 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 254 2 4 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 200 254 (accept_3_2 7 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 200 254 2 3 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 200 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 200 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 200 254 2 2 100 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 254
  (Polychromatic418967fa.accept_11_3_2_1_1_994 3 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 254 2 1 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 254 (accept_3_2 1 200 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 199 254 (Eq.refl Bool.true) (allA_of_3_0 56
  199 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 198 254 (Eq.refl Bool.true) (allA_succ_of_gcd 56 198
  254 2 28 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  55 198 254 (accept_3_2 55 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 198 254 2 27 99 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 198 254
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 53 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 198 254 2 26 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 198 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 198 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 198 254 2 25 99 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 198 254 (accept_3_2 49 198 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 198 254 2 24 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 198 254 (Polychromatic418967fa.accept_13_8_3_7_1_2455
  47 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 254 2 23 99 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 198 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 198 254 2 22 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 198 254 (accept_3_2 43 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 254 2 21 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 198 254 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 198 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 254 2 20 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 198 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 198 254 2 19 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 198 254 (accept_3_2 37 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 254 2 18 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 254 (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 198 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 254 2 17 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 198 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 198 254 2 16 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 198 254 (accept_3_2 31 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 254 2 15 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 198 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 254 2 14 99 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 198 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 198 254 2 13 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 198 254 (accept_3_2 25 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 254 2 12 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 254 (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 198 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 254 2 11 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 254 2 10 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 254 (accept_3_2 19 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 254 2 9 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 254 (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 198 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 254 2 8 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 254 2 7 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 254 (accept_3_2 13 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 254 2 6 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 254 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 198 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 254 2 5 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 254 2 4 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 254 (accept_3_2 7 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198
  254 2 3 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  198 254 (Polychromatic418967fa.accept_17_5_11_16_1_3257 5 198 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 198 254 2 2 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 198 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 198 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 254 2 1 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 254 (accept_3_2 1 198 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 197 254 (Eq.refl Bool.true) (allA_succ_of_accept 57 197 254 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 197 254 (accept_3_2 55 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 197 254 (Polychromatic418967fa.accept_24_6_5_14_1_13735 54 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 197 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 53 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 254 (accept_3_2 52 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 197 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 197 254 (accept_3_2 49 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 197 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 197 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 254 (accept_3_2 46 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 254 (accept_3_2 43 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 254 (accept_3_2 40 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 254 (accept_3_2 37 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 254 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 254 (accept_3_2 34 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 254 (accept_3_2 31 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 254 (Polychromatic418967fa.accept_18_11_17_2_1_6349 29 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 254 (accept_3_2 28 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 197 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 254
  (Polychromatic418967fa.accept_16_10_5_14_1_6173 26 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 197 254 (accept_3_2 25 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 197 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 197 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 197 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 254 (accept_3_2 22 197 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 254 (accept_3_2 19 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 254 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 254 (accept_3_2 16 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 254 (accept_3_2 13 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 254 (accept_3_2 10 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 254 (accept_3_2 7 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 254 (accept_3_2 4 197 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 197 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 254 (accept_3_2 1 197 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 196 254 (Eq.refl Bool.true) (allA_of_3_0
  59 196 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 195 254 (Eq.refl Bool.true) (allA_succ_of_accept 59
  195 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 195 254 (accept_3_2 58 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 195 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 195 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 195
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 254 (accept_3_2 55 195
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 195 254
  (Polychromatic418967fa.accept_12_6_3_2_1_743 54 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 195 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 254 (accept_3_2 52 195 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 195 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 195 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 195 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 195 254 (accept_3_2 49 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 195 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 195 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 254 (accept_3_2 46 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 195 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 195 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 195 254 (accept_3_2 43 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 195 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 254 (accept_3_2 40 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 195 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 195 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 195 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 254 (accept_3_2 37 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 195 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 195 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 254 (accept_3_2 34 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 195 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 195 254 (accept_3_2 31 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 195 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 254 (accept_3_2 28 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 254 (Polychromatic418967fa.accept_16_11_3_14_1_5043 27 195 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 254 (accept_3_2 25 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 195 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 195 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 254 (accept_3_2 22 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 195 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 254
  (Polychromatic418967fa.accept_21_20_6_2_1_11048 20 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 195 254 (accept_3_2 19 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 195 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 195 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 195 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 254 (accept_3_2 16 195 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 254 (accept_3_2 13 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 195 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 195 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 254 (accept_3_2 10 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 195 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 254 (accept_3_2 7 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  195 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 195 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 254 (accept_3_2 4 195 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 195 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 254
  (Polychromatic418967fa.accept_17_2_8_16_1_4403 2 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 254 (accept_3_2 1 195 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 194 254 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 194 254 2 30 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 194 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 194 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 194 254 2 29 97 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 194 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 194 254 2 28 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 194 254 (accept_3_2 55 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 194 254 2 27 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 194 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 194 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 194 254 2 26 97 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 194 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 194 254 2 25 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 194 254 (accept_3_2 49 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 194 254 2 24 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 194 254 (Polychromatic418967fa.accept_13_8_12_7_1_2442 47 194 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 194 254 2 23 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 194 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 194 254 2 22 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 194 254 (accept_3_2 43 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 254 2 21 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 254 (Polychromatic418967fa.accept_19_3_4_7_1_987 41 194 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 254 2 20 97 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 254 2 19 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 254 (accept_3_2 37 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 254 2 18 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 194 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 254 2 17 97 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 254 2 16 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 254 (accept_3_2 31 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 254 2 15 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 254 (Polychromatic418967fa.accept_18_11_14_2_1_5058 29 194 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 254 2 14 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 254
  (Polychromatic418967fa.accept_17_10_7_16_1_6841 27 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 194 254 2 13 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 194 254 (accept_3_2 25 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 254 2 12 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 254 (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 194 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 254 2 11 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 254 2 10 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 254 (accept_3_2 19 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 254 2 9 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 194 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 254 2 8 97 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 254 2 7 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 254 (accept_3_2 13 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 254 2 6 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 194 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 254 2 5 97 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 254
  (Polychromatic418967fa.accept_23_9_10_1_1_8974 9 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 254 2 4 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 254 (accept_3_2 7 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  254 2 3 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 254 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 194 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 254 2 2 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 194 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 254 2 1 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 254 (accept_3_2 1 194 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 193 254 (Eq.refl Bool.true)
  (allA_of_3_0 62 193 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 192 254 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 192 254 2 31 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 192 254 (accept_3_2 61 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 192 254 2 30 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 192 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 192 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 192 254 2 29 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 192 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 192 254 2 28 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 192 254 (accept_3_2 55 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 192 254 2 27 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 192 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 192 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 192 254 2 26 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 192 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 192 254 2 25 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 192 254 (accept_3_2 49 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 254 2 24 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 192 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 192 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 254 2 23 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 192 254
  (Polychromatic418967fa.accept_17_11_5_16_1_5600 45 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 192 254 2 22 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 192 254 (accept_3_2 43 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 254 2 21 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 192 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 192 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 254 2 20 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 254
  (Polychromatic418967fa.accept_11_6_5_1_1_586 39 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 192 254 2 19 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 192 254 (accept_3_2 37 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 254 2 18 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 192 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 254 2 17 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 192 254 2 16 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 192 254 (accept_3_2 31 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 254 2 15 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 192 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 192 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 254 2 14 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 192 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 192 254 2 13 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 192 254 (accept_3_2 25 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 254 2 12 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 192 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 192 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 254 2 11 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 254
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 192 254 2 10 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 192 254 (accept_3_2 19 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 254 2 9 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 192 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 254 2 8 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 192 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 192 254 2 7 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 254 (accept_3_2 13 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 254 2 6 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 192 254 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 192 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 254 2 5 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 254
  (Polychromatic418967fa.accept_15_9_12_14_1_963 9 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 254 2 4 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 254 (accept_3_2 7 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192
  254 2 3 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 192 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 192 254 2 2 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 192 254 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 192 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 254 2 1 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 254 (accept_3_2 1 192 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 191 254 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 191 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 191 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 191 254 (Polychromatic418967fa.accept_22_18_15_12_1_7530 62
  191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 191 254 (accept_3_2 61
  191 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 191 254
  (Polychromatic418967fa.accept_13_8_9_7_1_530 60 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 191 254 (Polychromatic418967fa.accept_19_2_1_7_1_8683 59 191 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 191 254 (accept_3_2 58 191 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 191 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 191 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 191 254 (accept_3_2 55 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 191 254 (Polychromatic418967fa.accept_13_2_9_7_1_164 54 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 191 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 191 254 (accept_3_2 52 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 191 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 191 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 254
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 50 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 191 254 (accept_3_2 49 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 191 254 (Polychromatic418967fa.accept_15_3_11_14_1_1705 48 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 191 254 (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 191 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 191 254 (accept_3_2 46 191 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 191 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 191 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 191 254 (accept_3_2 43 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 191 254 (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 191 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 254 (accept_3_2 40 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 191 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 254
  (Polychromatic418967fa.accept_25_13_16_4_1_15531 38 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 191 254 (accept_3_2 37 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 191 254 (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 254 (Polychromatic418967fa.accept_10_5_1_4_1_1444
  35 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 254 (accept_3_2 34
  191 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 191 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 191 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 254 (accept_3_2 31 191 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 191 254 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 191 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 254 (accept_3_2 28 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 254 (Polychromatic418967fa.accept_16_10_15_14_1_1086 26 191 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 254 (accept_3_2 25 191 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 254 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 191
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 254
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 23 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 191 254 (accept_3_2 22 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 191 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 191 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 191
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 254 (accept_3_2 19 191
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 254
  (Polychromatic418967fa.accept_14_4_9_2_1_95 18 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 191 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 191 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 254 (accept_3_2 16 191 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 191 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 254
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 191 254 (accept_3_2 13 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 191 254 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 254
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 254 (accept_3_2 10 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 254 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 254 (accept_3_2 7 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 254 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 191 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 254 (accept_3_2 4 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 254 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 254 (accept_3_2 1 191 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65
  190 254 (Eq.refl Bool.true) (allA_of_3_0 65 190 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 189 254
  (Eq.refl Bool.true) (allA_succ_of_accept 65 189 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 254 (accept_3_2 64 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 189 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 189 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 189 254
  (Polychromatic418967fa.accept_36_26_9_2_1_15530 62 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 189 254 (accept_3_2 61 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 189 254 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 189 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 189 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 254 (accept_3_2 58 189 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 189 254
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 189 254 (Polychromatic418967fa.accept_17_5_2_16_1_1294 56 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 189 254 (accept_3_2 55 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 189 254 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 189
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 189 254 (accept_3_2 52 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 189 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 189 254 (Polychromatic418967fa.accept_15_5_9_14_1_1724 50 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 254 (accept_3_2 49 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 189
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 254 (accept_3_2 46 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 189 254 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 189 254 (Polychromatic418967fa.accept_19_6_18_7_1_10032 44 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 254 (accept_3_2 43 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 189
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 254 (accept_3_2 40 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 189 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 189 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 254 (accept_3_2 37 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 189
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 254 (accept_3_2 34 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 189 254 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 254 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 254 (accept_3_2 31 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 189
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 254 (accept_3_2 28 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 189 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 254 (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 254 (accept_3_2 25 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 254 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 189
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 254 (accept_3_2 22 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 189 254 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 189 254 (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 254 (accept_3_2 19 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 189
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 254 (accept_3_2 16 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 254 (accept_3_2 13 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 254 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 189
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 254 (accept_3_2 10 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 254 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 189 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 254 (accept_3_2 7 189 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 254 (accept_3_2 4 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 254 (Polychromatic418967fa.accept_25_2_14_4_1_15529 2 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 254 (accept_3_2 1 189 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 67 188 254 (Eq.refl Bool.true) (allA_succ_of_gcd 66 188 254 2 33 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 188 254
  (Polychromatic418967fa.accept_12_5_8_2_1_309 65 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 188 254 2 32 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 188 254 (Polychromatic418967fa.accept_17_12_1_16_1_4360 63 188 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 188 254 2 31 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 188 254 (accept_3_2 61 188 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 188 254 2 30 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 188 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 188 254 2 29 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 188 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 188 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 188 254 2 28 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 188 254 (accept_3_2 55 188 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 188 254 2 27 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 188 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 53
  188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 188 254 2 26 94 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 188 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 188 254 2 25 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 188 254 (accept_3_2 49 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 188 254 2 24 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 188 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 188 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 188 254 2 23 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 188 254 2 22 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 188 254 (accept_3_2 43 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 188 254 2 21 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 188 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 188 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 254 2 20 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 254 2 19 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 254 (accept_3_2 37 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 254 2 18 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 188 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 188 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 254 2 17 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 188 254 2 16 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 188 254 (accept_3_2 31 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 188 254 2 15 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 188 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 188 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 254 2 14 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 254
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 188 254 2 13 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 188 254 (accept_3_2 25 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 254 2 12 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 188 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 188 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 254 2 11 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 254 2 10 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 188 254 (accept_3_2 19 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 188 254 2 9 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 188 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 188 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 254 2 8 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 254 2 7 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 254 (accept_3_2 13 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 254 2 6 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 188 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 188 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 254 2 5 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 254 2 4 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 254 (accept_3_2 7 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  254 2 3 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 188 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 254 2 2 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 188 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 188 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 254 2 1 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 254 (accept_3_2 1 188 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 187 254 (Eq.refl Bool.true)
  (allA_of_3_0 68 187 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 186 254 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 186 254 2 34 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 186 254 (accept_3_2 67 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 254 2 33 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 186 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 186 254 2 32 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 186 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 186 254 2 31 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 186 254 (accept_3_2 61 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 254 2 30 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 186 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 186 254 2 29 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 186 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 186 254 2 28 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 186 254 (accept_3_2 55 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 254 2 27 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 186 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 186 254 2 26 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 186 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 186 254 2 25 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 186 254 (accept_3_2 49 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 254 2 24 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 186 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 254 2 23 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 186 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 186 254 2 22 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 186 254 (accept_3_2 43 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 254 2 21 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 186 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 254 2 20 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 186 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 186 254 2 19 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 186 254 (accept_3_2 37 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 254 2 18 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 186 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 254 2 17 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 186 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 186 254 2 16 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 186 254 (accept_3_2 31 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 254 2 15 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 254 (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 186 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 254 2 14 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 254 2 13 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 254 (accept_3_2 25 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 254 2 12 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 186 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 254 2 11 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 254 2 10 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 254 (accept_3_2 19 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 254 2 9 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 186 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 254 2 8 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 254 2 7 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 254 (accept_3_2 13 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 254 2 6 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 254 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 186 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 254 2 5 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 254 2 4 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 254 (accept_3_2 7 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  254 2 3 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 186 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 254 2 2 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 186 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 254 2 1 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 254 (accept_3_2 1 186 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 185 254 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 185 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 185 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 185 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 185 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 185 254 (accept_3_2 67 185 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 185 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 66
  185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 185 254
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 185 254 (accept_3_2 64 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 185 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 185 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 185 254 (accept_3_2 61 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 185 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 185 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 185 254 (accept_3_2 58 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 185 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 185 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 185 254 (accept_3_2 55 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 185 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 185 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 185 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 185 254 (accept_3_2 52 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 185 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 185 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 185 254 (accept_3_2 49 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 185 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 185 254 (accept_3_2 46 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 185 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 185 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 185 254 (accept_3_2 43 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 185 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 185 254 (accept_3_2 40 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 185 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 185 254 (Polychromatic418967fa.accept_15_8_5_14_1_986 38 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 254 (accept_3_2 37 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 185 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 185 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 185 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 185 254 (accept_3_2 34 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 185 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 185 254 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 254 (accept_3_2 31 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 185 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 185 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 185 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 185 254 (accept_3_2 28 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 185 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 185 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 185 254 (accept_3_2 25 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 185 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 185 254 (accept_3_2 22 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 185 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 185 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 254 (accept_3_2 19 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 254 (Polychromatic418967fa.accept_17_1_15_16_1_2202 18 185 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 254 (accept_3_2 16 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 185 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 185 254 (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 254 (accept_3_2 13 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 185 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 185 254 (accept_3_2 10 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  185 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 185 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 254 (accept_3_2 7 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 185 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 185 254 (accept_3_2 4 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  185 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 185 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 185 254 (Polychromatic418967fa.accept_15_2_5_14_1_61 2 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 254 (accept_3_2 1 185 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 185 254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 184 254 (Eq.refl Bool.true) (allA_of_3_0 71 184 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 72 183 254 (Eq.refl Bool.true) (allA_succ_of_accept 71 183 254 (Polychromatic418967fa.accept_6_5_3_2_1_68
  71 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 254 (accept_3_2 70
  183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 183 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 183 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 183 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 183 254 (accept_3_2 67 183 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 183 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 183 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 254 (accept_3_2 64
  183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 183 254
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 183 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 183 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 183 254 (accept_3_2 61 183 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 183 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 183 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 254 (accept_3_2 58
  183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 183 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 183 254 (Polychromatic418967fa.accept_15_11_3_14_1_971 56 183 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 254 (accept_3_2 55 183 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 183 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 183 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 183 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 183 254 (accept_3_2 52 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 183 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 183 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 254 (accept_3_2 49 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 183 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 183 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 183 254 (accept_3_2 46 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 183 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 183 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 254 (accept_3_2 43 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 183 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 254 (accept_3_2 40 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 183 254 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 183 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 254 (accept_3_2 37 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 254 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 183 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 183 254 (accept_3_2 34 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 183 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 183 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 254 (accept_3_2 31 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 183 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 183 254 (accept_3_2 28 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 183 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 254 (accept_3_2 25 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 183 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 254 (accept_3_2 22 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 183 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 183 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 254 (accept_3_2 19 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 183 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 254 (accept_3_2 16 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 183 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 183 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 254 (accept_3_2 13 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 254 (Polychromatic418967fa.accept_17_12_13_16_1_3226 12 183 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 254 (accept_3_2 10 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 254 (accept_3_2 7 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 183 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 254 (accept_3_2 4 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 183 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 254 (Polychromatic418967fa.accept_15_2_3_14_1_972 2 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 254 (accept_3_2 1 183 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183 254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 73 182 254 (Eq.refl Bool.true) (allA_succ_of_gcd 72 182 254 2 36 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 182 254
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 182 254 2 35 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 182 254 (Polychromatic418967fa.accept_17_1_12_16_1_2211 69 182 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 182 254 2 34 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 182 254 (accept_3_2 67 182 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 182 254 2 33 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 182 254
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 182 254 2 32 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 182 254 (Polychromatic418967fa.accept_15_3_2_14_1_1713 63 182 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 182 254 2 31 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 182 254 (accept_3_2 61 182 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 182 254 2 30 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 182 254
  (Polychromatic418967fa.accept_21_17_14_2_1_4762 59 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 182 254 2 29 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 182 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 182 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 182 254 2 28 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 182 254 (accept_3_2 55 182 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 182 254 2 27 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 182 254
  (Polychromatic418967fa.accept_19_15_11_7_1_8711 53 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 182 254 2 26 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 182 254 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 182 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 182 254 2 25 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 182 254 (accept_3_2 49 182 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 182 254 2 24 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 182 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 47 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 182 254 2 23 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 182 254 (Polychromatic418967fa.accept_17_11_12_16_1_3219 45 182 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 182 254 2 22 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 182 254 (accept_3_2 43 182 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 182 254 2 21 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 182 254
  (Polychromatic418967fa.accept_21_20_14_2_1_6393 41 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 182 254 2 20 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 182 254 (Polychromatic418967fa.accept_22_17_6_12_1_5923 39 182 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 182 254 2 19 91 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 182 254 (accept_3_2 37
  182 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 182 254 2 18 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 182 254
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 182 254 2 17 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 182 254 (Polychromatic418967fa.accept_15_3_2_14_1_1713 33 182 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 182 254 2 16 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 182 254 (accept_3_2 31 182 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 182 254 2 15 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 182 254
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 182 254 2 14 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 182 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 182 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 182 254 2 13 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 182 254 (accept_3_2 25 182 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 182 254 2 12 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 182 254 (Polychromatic418967fa.accept_19_4_11_7_1_7210
  23 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 254 2 11 91 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 254
  (Polychromatic418967fa.accept_25_21_7_4_1_6458 21 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 254 2 10 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 254 (accept_3_2 19 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 254 2 9 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 182 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 254 2 8 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 254
  (Polychromatic418967fa.accept_19_15_11_7_1_8711 15 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 182 254 2 7 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 182 254 (accept_3_2 13 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 254 2 6 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 254 (Polychromatic418967fa.accept_17_11_12_16_1_3219 11 182 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 254 2 5 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 254
  (Polychromatic418967fa.accept_19_9_11_7_1_5836 9 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 254 2 4 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 254 (accept_3_2 7 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  254 2 3 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 254 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 182 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 254 2 2 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 254 (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 182 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 254 2 1 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 254 (accept_3_2 1 182 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 181 254 (Eq.refl
  Bool.true) (allA_of_3_0 74 181 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 180 254 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 180 254 2 37 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 180 254 (accept_3_2 73 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 180 254 2 36 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 180 254 (Polychromatic418967fa.accept_16_7_4_14_1_2860 71 180 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 180 254 2 35 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 180 254
  (Polychromatic418967fa.accept_13_4_11_7_1_558 69 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 180 254 2 34 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 180 254 (accept_3_2 67 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 254 2 33 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 180 254 (Polychromatic418967fa.accept_16_1_4_14_1_1896 65 180 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 180 254 2 32 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 180 254
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 180 254 2 31 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 180 254 (accept_3_2 61 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 254 2 30 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 180 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 180 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 254 2 29 90 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 180 254
  (Polychromatic418967fa.accept_13_5_11_7_1_559 57 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 180 254 2 28 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 180 254 (accept_3_2 55 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 180 254 2 27 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 180 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 180 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 254 2 26 90 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 180 254
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 180 254 2 25 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 180 254 (accept_3_2 49 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 254 2 24 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 254 (Polychromatic418967fa.accept_16_15_4_14_1_6123 47 180 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 254 2 23 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 180 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 180 254 2 22 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 180 254 (accept_3_2 43 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 254 2 21 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 254 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 180 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 254 2 20 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 180 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 180 254 2 19 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 180 254 (accept_3_2 37 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 254 2 18 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 180 254 (Polychromatic418967fa.accept_13_9_11_7_1_1077 35 180 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 254 2 17 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 254
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 33 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 180 254 2 16 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 180 254 (accept_3_2 31 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 254 2 15 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 254 (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 180 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 254 2 14 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 254
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 180 254 2 13 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 180 254 (accept_3_2 25 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 254 2 12 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 254 (Polychromatic418967fa.accept_16_7_4_14_1_2860 23 180 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 254 2 11 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 254
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 21 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 180 254 2 10 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 180 254 (accept_3_2 19 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 254 2 9 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 180 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 254 2 8 90 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 180 254
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 15 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 180 254 2 7 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 180 254 (accept_3_2 13 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 254 2 6 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 180 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 180 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 254 2 5 90 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 254
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 254 2 4 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 254 (accept_3_2 7 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180
  254 2 3 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  180 254 (Polychromatic418967fa.accept_13_5_11_7_1_559 5 180 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 180 254 2 2 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 180 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 180 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 254 2 1 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 254 (accept_3_2 1 180 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 179 254 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 179 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 179 254
  (Polychromatic418967fa.accept_17_6_9_16_1_4410 74 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 179 254 (accept_3_2 73 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 179 254 (Polychromatic418967fa.accept_19_15_8_7_1_11482 72 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 179 254 (Polychromatic418967fa.accept_19_14_8_7_1_12706 71 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 179 254 (accept_3_2 70 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 179 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 179 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 179 254 (accept_3_2 67 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 179 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 179 254 (accept_3_2 64 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 179 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 179 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 179 254 (accept_3_2 61 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 179 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 179 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 179 254 (accept_3_2 58 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 179 254 (accept_3_2 55 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 179 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 254 (accept_3_2 52 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 179 254 (accept_3_2 49 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 179 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 179 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 254 (accept_3_2 46 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 179 254 (accept_3_2 43 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 179 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 254 (accept_3_2 40 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 254
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 179 254 (accept_3_2 37 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 179 254 (Polychromatic418967fa.accept_22_14_3_12_1_15528 36 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 254 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 254 (accept_3_2 34 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 179 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 254 (accept_3_2 31 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 254 (accept_3_2 28 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 254 (accept_3_2 25 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 254 (accept_3_2 22 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 254 (accept_3_2 19 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 254 (accept_3_2 16 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 254 (accept_3_2 13 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 254 (Polychromatic418967fa.accept_16_11_3_14_1_5043 11 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 254 (accept_3_2 10 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 254
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 254 (accept_3_2 7 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 254 (accept_3_2 4 179 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 254
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 254 (accept_3_2 1 179 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 178 254 (Eq.refl
  Bool.true) (allA_of_3_0 77 178 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 177 254 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 177 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 177 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 177 254 (accept_3_2 76 177 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 177 254 (Polychromatic418967fa.accept_13_9_8_7_1_1073
  74 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 254 (accept_3_2 73
  177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 177 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 72 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 177 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 177 254 (accept_3_2 70 177 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 177 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 69 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 177 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 177 254 (accept_3_2 67 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 177 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 177 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 254 (accept_3_2 64 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 177 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 177 254 (accept_3_2 61 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 177 254 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 254 (accept_3_2 58 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 177 254
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 56 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 177 254 (accept_3_2 55 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 177 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 177 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 177 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 254 (accept_3_2 52 177 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 177 254 (accept_3_2 49 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 177 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 254 (accept_3_2 46 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 254 (Polychromatic418967fa.accept_16_13_1_14_1_2855 45 177 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 177 254 (accept_3_2 43 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 177 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 177 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 254 (accept_3_2 40 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 254
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 38 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 177 254 (accept_3_2 37 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 177 254 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 254 (accept_3_2 34 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 177 254 (accept_3_2 31 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 177 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 177 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 254 (accept_3_2 28 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 254 (accept_3_2 25 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 177 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 254 (accept_3_2 22 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 254
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 20 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 254 (accept_3_2 19 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 177 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 177 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 254 (accept_3_2 16 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 254 (accept_3_2 13 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 177 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 254 (accept_3_2 10 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 254 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 254 (accept_3_2 7 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  177 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 177 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 254 (accept_3_2 4 177 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 254 (accept_3_2 1 177 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 176 254 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 176 254 2 39 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 176 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 176 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 176 254 2 38 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 176 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 176 254 2 37 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 176 254 (accept_3_2 73 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 176 254 2 36 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 176 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 176 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 176 254 2 35 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 176 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 176 254 2 34 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 176 254 (accept_3_2 67 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 176 254 2 33 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 176 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 176 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 176 254 2 32 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 176 254
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 176 254 2 31 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 176 254 (accept_3_2 61 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 176 254 2 30 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 176 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 176 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 176 254 2 29 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 176 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 176 254 2 28 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 176 254 (accept_3_2 55 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 176 254 2 27 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 176 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 176 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 254 2 26 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 176 254 2 25 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 176 254 (accept_3_2 49 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 254 2 24 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 176 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 254 2 23 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 254 2 22 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 254 (accept_3_2 43 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 254 2 21 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 176 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 254 2 20 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 254 2 19 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 254 (accept_3_2 37 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 254 2 18 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 176 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 176 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 254 2 17 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 176 254 2 16 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 176 254 (accept_3_2 31 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 176 254 2 15 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 176 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 176 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 254 2 14 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 176 254 2 13 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 176 254 (accept_3_2 25 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 254 2 12 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 176 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 176 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 254 2 11 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 254 2 10 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 176 254 (accept_3_2 19 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 176 254 2 9 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 176 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 176 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 254 2 8 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 254 2 7 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 254 (accept_3_2 13 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 254 2 6 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 176 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 176 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 254 2 5 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 254
  (Polychromatic418967fa.accept_17_9_6_16_1_3280 9 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 254 2 4 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 254 (accept_3_2 7 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  254 2 3 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 176 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 254 2 2 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 176 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 176 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 254 2 1 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 254 (accept_3_2 1 176 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 175 254 (Eq.refl
  Bool.true) (allA_of_3_0 80 175 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 174 254 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 174 254 2 40 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 174 254 (accept_3_2 79 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 174 254 2 39 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 174 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 174 254 2 38 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 174 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 174 254 2 37 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 174 254 (accept_3_2 73 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 254 2 36 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 174 254 2 35 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 174 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 174 254 2 34 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 174 254 (accept_3_2 67 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 254 2 33 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 254 (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 174 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 174 254 2 32 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 174 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 174 254 2 31 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 174 254 (accept_3_2 61 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 254 2 30 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 254 2 29 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 174 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 174 254 2 28 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 174 254 (accept_3_2 55 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 254 2 27 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 254 2 26 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 174 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 174 254 2 25 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 174 254 (accept_3_2 49 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 254 2 24 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 254 (Polychromatic418967fa.accept_27_20_12_11_1_7817 47 174 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 254 2 23 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 174 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 174 254 2 22 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 174 254 (accept_3_2 43 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 254 2 21 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 254 2 20 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 174 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 174 254 2 19 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 174 254 (accept_3_2 37 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 254 2 18 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 254 2 17 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 174 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 174 254 2 16 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 174 254 (accept_3_2 31 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 254 2 15 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 254 2 14 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 254 2 13 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 254 (accept_3_2 25 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 254 2 12 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 254 2 11 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 254
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 254 2 10 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 254 (accept_3_2 19 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 254 2 9 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 254 2 8 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 254 2 7 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 254 (accept_3_2 13 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 254 2 6 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 174 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 254 2 5 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 254 2 4 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 254 (accept_3_2 7 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  254 2 3 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 174 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 254 2 2 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 174 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 254 2 1 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 254 (accept_3_2 1 174 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 173 254 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 173 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 173 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 80
  173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 173 254 (accept_3_2 79
  173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 173 254
  (Polychromatic418967fa.accept_23_9_12_1_1_12155 78 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 173 254 (Polychromatic418967fa.accept_10_7_3_4_1_978 77 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 173 254 (accept_3_2 76 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 173 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 173 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 74 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 173 254 (accept_3_2 73 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 173 254 (Polychromatic418967fa.accept_17_4_3_16_1_9483 72 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 173 254 (accept_3_2 70 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 173 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 173 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 68 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 173 254 (accept_3_2 67 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 173 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 173 254 (Polychromatic418967fa.accept_15_5_8_14_1_432 65 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 173 254 (accept_3_2 64 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 173 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 173 254
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 62 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 173 254 (accept_3_2 61 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 173 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 254 (accept_3_2 58 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 173 254 (accept_3_2 55 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 173 254 (Polychromatic418967fa.accept_15_9_8_14_1_1699 54 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 173 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 254 (accept_3_2 52 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 254
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 50 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 254 (accept_3_2 49 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 254 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 254 (accept_3_2 46 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 254 (accept_3_2 43 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 254 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 254 (Polychromatic418967fa.accept_17_7_3_16_1_2208 41 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 254 (accept_3_2 40 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 173 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 254 (accept_3_2 37 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 254 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 254 (accept_3_2 34 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 254 (accept_3_2 31 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 254 (Polychromatic418967fa.accept_17_13_3_16_1_5599 30 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 254 (Polychromatic418967fa.accept_10_9_3_4_1_985 29 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 254 (accept_3_2 28 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 173 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 254
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 254 (accept_3_2 25 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 254 (accept_3_2 22 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 254 (accept_3_2 19 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 254 (accept_3_2 16 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 254
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 173 254 (accept_3_2 13 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 173 254 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 173 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 254 (accept_3_2 10 173 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 254 (accept_3_2 7 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 254 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 254 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 254 (accept_3_2 4 173 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 254
  (Polychromatic418967fa.accept_22_2_19_12_1_7598 2 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 254 (accept_3_2 1 173 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 172 254 (Eq.refl
  Bool.true) (allA_of_3_0 83 172 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 171 254 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 171 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 171 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 171 254 (accept_3_2 82 171 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 171 254
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 80 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 171 254 (accept_3_2 79 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 171 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 171 254 (accept_3_2 76 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 171 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 171 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 171 254
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 74 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 171 254 (accept_3_2 73 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 171 254 (Polychromatic418967fa.accept_21_9_3_2_1_6363 72 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 171 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 254 (accept_3_2 70 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 171 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 171 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 171 254 (accept_3_2 67 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 171 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 254 (accept_3_2 64 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 171 254 (Polychromatic418967fa.accept_17_12_1_16_1_4360 63 171 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 171 254 (accept_3_2 61 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 171 254 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 171 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 254 (accept_3_2 58 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 171 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 254
  (Polychromatic418967fa.accept_17_5_1_16_1_4359 56 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 171 254 (accept_3_2 55 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 171 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 254 (accept_3_2 52 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 171 254 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 171 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 171 254 (accept_3_2 49 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 171 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 171 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 254 (accept_3_2 46 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 171 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 254
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 44 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 171 254 (accept_3_2 43 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 171 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 254 (accept_3_2 40 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 254 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 171 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 254
  (Polychromatic418967fa.accept_11_5_6_1_1_988 38 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 171 254 (accept_3_2 37 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 171 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 171 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 254 (accept_3_2 34 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 171 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 254
  (Polychromatic418967fa.accept_17_15_1_16_1_8166 32 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 171 254 (accept_3_2 31 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 171 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 171 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 171 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 254 (accept_3_2 28 171 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 254 (Polychromatic418967fa.accept_7_6_3_2_1_461
  27 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 254 (accept_3_2 25 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 171 254 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 171 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 254 (accept_3_2 22 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 171 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 254 (accept_3_2 19 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 171 254 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 254 (accept_3_2 16 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 171 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 254
  (Polychromatic418967fa.accept_21_14_3_2_1_12567 14 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 171 254 (accept_3_2 13 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 171 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 171 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 254 (accept_3_2 10 171 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 254 (accept_3_2 7 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  171 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 171 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 254 (accept_3_2 4 171 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 254 (Polychromatic418967fa.accept_16_3_11_14_1_446 3 171 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 254
  (Polychromatic418967fa.accept_17_2_1_16_1_6946 2 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 254 (accept_3_2 1 171 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 170 254
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 170 254 2 42 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 170 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 83 170 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 170 254 2 41 85 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 170 254
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 170 254 2 40 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 170 254 (accept_3_2 79 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 170 254 2 39 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 170 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 170 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 170 254 2 38 85 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 170 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 170 254 2 37 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 170 254 (accept_3_2 73 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 170 254 2 36 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 170 254 (Polychromatic418967fa.accept_13_6_1_7_1_1690 71 170 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 170 254 2 35 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 170 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 170 254 2 34 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 170 254 (accept_3_2 67 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 170 254 2 33 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 170 254 (Polychromatic418967fa.accept_19_8_18_7_1_3143 65 170 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 170 254 2 32 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 254
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 170 254 2 31 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 170 254 (accept_3_2 61 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 254 2 30 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 170 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 254 2 29 85 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 254 2 28 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 170 254 (accept_3_2 55 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 170 254 2 27 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 170 254 (Polychromatic418967fa.accept_15_8_5_14_1_986 53 170 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 254 2 26 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 254 2 25 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 254 (accept_3_2 49 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 254 2 24 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 254 (Polychromatic418967fa.accept_13_8_1_7_1_2505 47 170 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 254 2 23 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 254
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 254 2 22 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 254 (accept_3_2 43 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 254 2 21 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 170 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 254 2 20 85 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 254 2 19 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 254 (accept_3_2 37 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 254 2 18 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 254 (Polychromatic418967fa.accept_18_17_8_2_1_2622 35 170 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 254 2 17 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 254 2 16 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 254 (accept_3_2 31 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 254 2 15 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 254 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 170 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 254 2 14 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 254
  (Polychromatic418967fa.accept_19_8_18_7_1_3143 27 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 254 2 13 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 254 (accept_3_2 25 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 254 2 12 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 170 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 254 2 11 85 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 254 2 10 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 254 (accept_3_2 19 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 254 2 9 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 170 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 254 2 8 85 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 254 2 7 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 254 (accept_3_2 13 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 254 2 6 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 254 (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 170 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 254 2 5 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 254
  (Polychromatic418967fa.accept_15_9_5_14_1_973 9 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 254 2 4 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 254 (accept_3_2 7 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  254 2 3 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 170 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 254 2 2 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 170 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 254 2 1 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 254 (accept_3_2 1 170 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 169 254
  (Eq.refl Bool.true) (allA_of_3_0 86 169 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 168 254 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 168 254 2 43 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 168 254 (accept_3_2 85 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 168 254 2 42 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 168 254 (Polychromatic418967fa.accept_13_5_12_7_1_1080 83 168 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 168 254 2 41 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 168 254
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 81 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 168 254 2 40 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 168 254 (accept_3_2 79 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 168 254 2 39 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 168 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 168 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 168 254 2 38 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 168 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 168 254 2 37 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 168 254 (accept_3_2 73 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 168 254 2 36 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 168 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 168 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 254 2 35 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 168 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 69 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 168 254 2 34 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 168 254 (accept_3_2 67 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 254 2 33 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 254 (Polychromatic418967fa.accept_17_14_15_16_1_1271 65 168 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 254 2 32 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 168 254
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 63 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 168 254 2 31 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 168 254 (accept_3_2 61 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 254 2 30 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 168 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 254 2 29 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 168 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 168 254 2 28 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 168 254 (accept_3_2 55 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 254 2 27 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 168 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 254 2 26 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 168 254
  (Polychromatic418967fa.accept_27_24_6_11_1_15527 51 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 168 254 2 25 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 168 254 (accept_3_2 49 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 254 2 24 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 254 (Polychromatic418967fa.accept_13_8_12_7_1_2442 47 168 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 254 2 23 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 168 254
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 168 254 2 22 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 168 254 (accept_3_2 43 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 254 2 21 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 168 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 254 2 20 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 168 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 168 254 2 19 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 168 254 (accept_3_2 37 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 254 2 18 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 168 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 168 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 254 2 17 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 254
  (Polychromatic418967fa.accept_20_13_8_14_1_1467 33 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 168 254 2 16 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 168 254 (accept_3_2 31 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 254 2 15 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 168 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 254 2 14 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 254
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 27 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 168 254 2 13 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 168 254 (accept_3_2 25 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 254 2 12 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 168 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 254 2 11 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 254 2 10 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 168 254 (accept_3_2 19 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 254 2 9 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 168 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 254 2 8 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 254
  (Polychromatic418967fa.accept_20_15_8_14_1_14036 15 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 254 2 7 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 254 (accept_3_2 13 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 254 2 6 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 254 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 168 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 254 2 5 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 254 2 4 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 254 (accept_3_2 7 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168
  254 2 3 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  168 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 168 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 254 2 2 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 168 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 168 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 254 2 1 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 254 (accept_3_2 1 168 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 167 254
  (Eq.refl Bool.true) (allA_succ_of_accept 87 167 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 167 254
  (Polychromatic418967fa.accept_25_11_17_4_1_15507 86 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 167 254 (accept_3_2 85 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 167 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 167 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 167 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 83 167
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 167 254 (accept_3_2 82 167
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3
  81 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 167 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 167 254 (accept_3_2 79 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 167 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 167 254 (accept_3_2 76 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 167 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 167 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 167 254 (accept_3_2 73 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 167 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 167 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 167 254 (accept_3_2 70 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 167 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 167 254 (accept_3_2 67 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 167 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 167 254 (accept_3_2 64 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 167 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 167 254 (accept_3_2 61 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 167 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 167 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 254 (accept_3_2 58 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 254 (accept_3_2 55 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 254 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 254 (accept_3_2 52 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 167 254 (accept_3_2 49 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 167 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 167 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 254 (accept_3_2 46 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 167 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 254 (accept_3_2 43 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 254 (accept_3_2 40 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 254 (accept_3_2 37 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 254 (accept_3_2 34 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 254 (accept_3_2 31 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 254 (accept_3_2 28 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 254 (accept_3_2 25 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 254 (accept_3_2 22 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 167 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 254 (accept_3_2 19 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 254 (accept_3_2 16 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 254
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 254 (accept_3_2 13 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 254 (accept_3_2 10 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 254 (accept_3_2 7 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 254 (accept_3_2 4 167 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 254 (accept_3_2 1 167 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 166 254
  (Eq.refl Bool.true) (allA_of_3_0 89 166 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 165 254 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 165 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 165 254 (accept_3_2 88 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 165 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 86 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 165 254 (accept_3_2 85 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 165 254 (Polychromatic418967fa.accept_13_6_9_7_1_2430 84 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 165 254 (accept_3_2 82 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 165 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 81 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 165 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 80 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 165 254 (accept_3_2 79 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 165 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 165 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 165 254 (accept_3_2 76 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 165 254
  (Polychromatic418967fa.accept_16_10_5_14_1_6173 74 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 165 254 (accept_3_2 73 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 165 254 (Polychromatic418967fa.accept_19_15_13_7_1_7246 72 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 254 (accept_3_2 70
  165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 165 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 165 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 165 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 254 (accept_3_2 67 165 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 165 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 165 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 254 (accept_3_2 64 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 165 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 254 (accept_3_2 61 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 254 (accept_3_2 58 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 165 254 (Polychromatic418967fa.accept_16_9_5_14_1_6126 57 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 165 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 254 (accept_3_2 55 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 165 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 254 (accept_3_2 52 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 165 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 254 (accept_3_2 49 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 254 (accept_3_2 46 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 165 254 (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 165 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 254 (accept_3_2 43 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 254 (accept_3_2 40 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 254 (Polychromatic418967fa.accept_25_13_15_4_1_15526 38 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 254 (accept_3_2 37 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 165
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 165 254 (accept_3_2 34 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 165 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 165 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 254 (accept_3_2 31 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 254 (accept_3_2 28 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 254 (accept_3_2 25 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 254 (accept_3_2 22 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 165 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 254 (accept_3_2 19 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 254 (accept_3_2 16 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 254 (accept_3_2 13 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 254 (accept_3_2 10 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  165 254 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 254 (accept_3_2 7 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 165 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 254 (accept_3_2 4 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 254 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 254 (accept_3_2 1 165 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 164 254
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 164 254 2 45 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 164 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 164 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 164 254 2 44 82 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 164 254
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 87 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 164 254 2 43 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 164 254 (accept_3_2 85 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 164 254 2 42 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 164 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 164 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 164 254 2 41 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 164 254
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 81 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 164 254 2 40 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 164 254 (accept_3_2 79 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 164 254 2 39 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 164 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 164 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 164 254 2 38 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 164 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 164 254 2 37 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 164 254 (accept_3_2 73 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 164 254 2 36 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 164 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 164 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 254 2 35 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 254 2 34 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 254 (accept_3_2 67 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 254 2 33 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 164 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 254 2 32 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 254
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 63 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 164 254 2 31 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 164 254 (accept_3_2 61 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 254 2 30 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 164 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 254 2 29 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 254 2 28 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 254 (accept_3_2 55 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 254 2 27 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 164 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 254 2 26 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 254
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 254 2 25 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 254 (accept_3_2 49 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 254 2 24 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 164 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 254 2 23 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 254
  (Polychromatic418967fa.accept_21_3_17_2_1_11043 45 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 164 254 2 22 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 164 254 (accept_3_2 43 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 254 2 21 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 164 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 254 2 20 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 254
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 39 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 254 2 19 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 254 (accept_3_2 37 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 254 2 18 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 164 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 164 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 254 2 17 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 254 2 16 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 164 254 (accept_3_2 31 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 164 254 2 15 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 164 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 254 2 14 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 254 2 13 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 254 (accept_3_2 25 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 254 2 12 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 164 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 254 2 11 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 254
  (Polychromatic418967fa.accept_23_21_3_1_1_7150 21 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 254 2 10 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 254 (accept_3_2 19 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 254 2 9 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 164 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 164 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 254 2 8 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 254 2 7 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 254 (accept_3_2 13 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 254 2 6 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 164 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 164 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 254 2 5 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 254 2 4 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 254 (accept_3_2 7 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  254 2 3 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 164 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 254 2 2 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 164 254 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 164 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 254 2 1 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 254 (accept_3_2 1 164 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 163 254
  (Eq.refl Bool.true) (allA_of_3_0 92 163 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 162 254 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 162 254 2 46 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 162 254 (accept_3_2 91 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 162 254 2 45 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 162 254 (Polychromatic418967fa.accept_22_1_8_12_1_5938 89 162 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 162 254 2 44 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 162 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 162 254 2 43 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 162 254 (accept_3_2 85 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 162 254 2 42 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 162 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 162 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 162 254 2 41 81 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 162 254
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 162 254 2 40 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 162 254 (accept_3_2 79 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 254 2 39 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 162 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 162 254 2 38 81 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 162 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 162 254 2 37 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 162 254 (accept_3_2 73 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 254 2 36 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 162 254 (Polychromatic418967fa.accept_14_1_8_2_1_1675 71 162 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 254 2 35 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 162 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 162 254 2 34 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 162 254 (accept_3_2 67 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 254 2 33 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 254 (Polychromatic418967fa.accept_22_21_8_12_1_15525 65 162 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 254 2 32 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 162 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 162 254 2 31 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 162 254 (accept_3_2 61 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 254 2 30 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 162 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 254 2 29 81 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 162 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 162 254 2 28 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 162 254 (accept_3_2 55 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 254 2 27 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 254 (Polychromatic418967fa.accept_13_1_6_7_1_550 53 162 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 254 2 26 81 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 162 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 162 254 2 25 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 162 254 (accept_3_2 49 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 254 2 24 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 162 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 254 2 23 81 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 254 2 22 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 254 (accept_3_2 43 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 254 2 21 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 162 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 254 2 20 81 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 254 2 19 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 254 (accept_3_2 37 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 254 2 18 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 254 (Polychromatic418967fa.accept_13_9_6_7_1_551 35 162 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 254 2 17 81 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 254 2 16 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 254 (accept_3_2 31 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 254 2 15 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 254 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 162 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 254 2 14 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 254 2 13 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 254 (accept_3_2 25 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 254 2 12 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 254 (Polychromatic418967fa.accept_17_6_9_16_1_4410 23 162 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 254 2 11 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 254 2 10 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 254 (accept_3_2 19 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 254 2 9 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 162 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 254 2 8 81 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 254
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 254 2 7 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 254 (accept_3_2 13 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 254 2 6 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 254 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 162 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 254 2 5 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 254 2 4 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 254 (accept_3_2 7 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  254 2 3 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 254 (Polychromatic418967fa.accept_19_5_10_7_1_5887 5 162 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 254 2 2 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 162 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 254 2 1 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 254 (accept_3_2 1 162 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 161
  254 (Eq.refl Bool.true) (allA_succ_of_accept 93 161 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 161 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 92 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 161 254 (accept_3_2 91 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 161 254 (Polychromatic418967fa.accept_13_12_5_7_1_1696 90 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 161 254 (Polychromatic418967fa.accept_13_11_5_7_1_2420 89 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 161 254 (accept_3_2 88 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 161 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 161 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 161 254 (accept_3_2 85 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 161 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 254 (accept_3_2 82 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 161 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 80 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 161 254 (accept_3_2 79 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 161 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 161 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 254 (accept_3_2 76 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 254
  (Polychromatic418967fa.accept_19_17_9_7_1_3171 74 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 161 254 (accept_3_2 73 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 161 254 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 254 (accept_3_2 70 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 254 (accept_3_2 67 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 254 (Polychromatic418967fa.accept_10_5_1_4_1_1444 65 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 254 (accept_3_2 64 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 161 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 254
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 62 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 254 (accept_3_2 61 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 254 (accept_3_2 58 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 254 (accept_3_2 55 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 254 (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 254 (Polychromatic418967fa.accept_17_2_8_16_1_4403 53 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 254 (accept_3_2 52 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 161 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 254 (accept_3_2 49 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 254 (accept_3_2 46 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 254 (accept_3_2 43 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 254 (accept_3_2 40 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 254
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 38 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 254 (accept_3_2 37 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 254 (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 254 (accept_3_2 34 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 254 (accept_3_2 31 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 254 (Polychromatic418967fa.accept_16_13_1_14_1_2855 29 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 254 (accept_3_2 28 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 254
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 254 (accept_3_2 25 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 254 (accept_3_2 22 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 254 (accept_3_2 19 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 254 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 254 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 254 (accept_3_2 16 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 254 (accept_3_2 13 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 254 (accept_3_2 10 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 254 (accept_3_2 7 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 254 (accept_3_2 4 161 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 254
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 254 (accept_3_2 1 161 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 160
  254 (Eq.refl Bool.true) (allA_of_3_0 95 160 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 159 254
  (Eq.refl Bool.true) (allA_succ_of_accept 95 159 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 159 254 (accept_3_2 94 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 159 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 159 254
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 92 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 159 254 (accept_3_2 91 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 159 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 90 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 159 254 (accept_3_2 88 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 159 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 159 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 86 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 159 254 (accept_3_2 85 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 159 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 159 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 159 254 (accept_3_2 82 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 159 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 80 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 159 254 (accept_3_2 79 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 159 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 78 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 254 (accept_3_2 76 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 159 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 74 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 159 254 (accept_3_2 73 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 159 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 159 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 254 (accept_3_2 70 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 159 254 (accept_3_2 67 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 159 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 254 (accept_3_2 64 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 254 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 254 (accept_3_2 61 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 159 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 159 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 254 (accept_3_2 58 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 254
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 56 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 159 254 (accept_3_2 55 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 159 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 254 (accept_3_2 52 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 254 (Polychromatic418967fa.accept_15_6_9_14_1_3457 51 159 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 254 (accept_3_2 49 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 159 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 159 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 254 (accept_3_2 46 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 254 (accept_3_2 43 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 159 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 254 (accept_3_2 40 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 254 (accept_3_2 37 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 159 254 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 159 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 254 (accept_3_2 34 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 254 (accept_3_2 31 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 159 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 254 (accept_3_2 28 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 254 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 254 (accept_3_2 25 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 159 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 254 (accept_3_2 22 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 254
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 254 (accept_3_2 19 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 159 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 254 (accept_3_2 16 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 254 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 254 (accept_3_2 13 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 254 (accept_3_2 10 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 254 (accept_3_2 7 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 254 (accept_3_2 4 159 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 159 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 254
  (Polychromatic418967fa.accept_22_2_5_12_1_15516 2 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 254 (accept_3_2 1 159 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 158
  254 (Eq.refl Bool.true) (allA_succ_of_gcd 96 158 254 2 48 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 158 254 (Polychromatic418967fa.accept_15_5_8_14_1_432 95 158
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 158 254 2 47 79 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 158 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 93 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 158 254 2 46 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 158 254 (accept_3_2 91 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 158 254 2 45 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 158 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 158 254 2 44 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 158 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 158 254 2 43 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 158 254 (accept_3_2 85 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 158 254 2 42 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 158 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 158 254 2 41 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 254
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 81 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 158 254 2 40 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 158 254 (accept_3_2 79 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 158 254 2 39 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 158 254 (Polychromatic418967fa.accept_19_1_6_7_1_2019 77 158 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 254 2 38 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 158 254 2 37 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 254 (accept_3_2 73 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 254 2 36 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 254 2 35 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 254 2 34 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 254 (accept_3_2 67 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 254 2 33 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 254 (Polychromatic418967fa.accept_14_9_4_2_1_983 65 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 254 2 32 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 254
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 254 2 31 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 254 (accept_3_2 61 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 254 2 30 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 254 2 29 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 254 2 28 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 254 (accept_3_2 55 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 254 2 27 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 254 2 26 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 254 2 25 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 254 (accept_3_2 49 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 254 2 24 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 254 2 23 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 254
  (Polychromatic418967fa.accept_17_11_5_16_1_5600 45 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 158 254 2 22 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 158 254 (accept_3_2 43 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 254 2 21 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 254 2 20 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 254 2 19 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 254 (accept_3_2 37 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 254 2 18 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 254 2 17 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 254 2 16 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 254 (accept_3_2 31 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 254 2 15 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 254 2 14 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 254 2 13 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 254 (accept_3_2 25 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 254 2 12 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 254 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 254 2 11 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 254 2 10 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 254 (accept_3_2 19 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 254 2 9 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 158 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 254 2 8 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 254 2 7 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 254 (accept_3_2 13 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 254 2 6 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 254 (Polychromatic418967fa.accept_17_11_5_16_1_5600 11 158 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 254 2 5 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 254 2 4 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 254 (accept_3_2 7 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  254 2 3 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 158 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 254 2 2 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 158 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 254 2 1 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 254 (accept_3_2 1 158 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  157 254 (Eq.refl Bool.true) (allA_of_3_0 98 157 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 156 254
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 156 254 2 49 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 156 254 (accept_3_2 97 156 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 156 254 2 48 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 156 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 95 156 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 156 254 2 47 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 156 254
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 93 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 156 254 2 46 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 156 254 (accept_3_2 91 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 156 254 2 45 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 156 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 156 254 2 44 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 156 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 87 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 156 254 2 43 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 156 254 (accept_3_2 85 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 156 254 2 42 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 254 (Polychromatic418967fa.accept_15_8_6_14_1_975 83 156 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 156 254 2 41 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 156 254
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 81 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 156 254 2 40 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 156 254 (accept_3_2 79 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 254 2 39 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 156 254 2 38 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 156 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 75 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 156 254 2 37 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 156 254 (accept_3_2 73 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 254 2 36 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 254 2 35 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 156 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 156 254 2 34 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 156 254 (accept_3_2 67 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 254 2 33 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 254 2 32 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 254
  (Polychromatic418967fa.accept_22_19_2_12_1_9192 63 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 156 254 2 31 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 156 254 (accept_3_2 61 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 254 2 30 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 254 2 29 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 254
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 57 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 156 254 2 28 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 254 (accept_3_2 55 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 254 2 27 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 254 2 26 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 254 2 25 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 254 (accept_3_2 49 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 254 2 24 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 254 2 23 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 254 2 22 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 254 (accept_3_2 43 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 254 2 21 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 254 2 20 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 254
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 254 2 19 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 254 (accept_3_2 37 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 254 2 18 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 254 2 17 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 156 254 2 16 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 156 254 (accept_3_2 31 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 254 2 15 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 254 (Polychromatic418967fa.accept_23_6_18_1_1_15524 29 156 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 254 2 14 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 254
  (Polychromatic418967fa.accept_21_6_9_2_1_9554 27 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 254 2 13 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 254 (accept_3_2 25 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 254 2 12 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 254 2 11 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 254
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 254 2 10 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 156 254 (accept_3_2 19 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 254 2 9 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 156 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 254 2 8 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 156 254 2 7 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 156 254 (accept_3_2 13 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 254 2 6 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 254 (Polychromatic418967fa.accept_19_11_4_7_1_1029 11 156 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 254 2 5 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 254
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 254 2 4 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 254 (accept_3_2 7 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156
  254 2 3 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  156 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 156 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 254 2 2 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 156 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 156 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 254 2 1 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 254 (accept_3_2 1 156 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  155 254 (Eq.refl Bool.true) (allA_succ_of_accept 99 155 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 155 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 155 254
  (Polychromatic418967fa.accept_15_8_5_14_1_986 98 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 155 254 (accept_3_2 97 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 155 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 96 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 155 254 (Polychromatic418967fa.accept_13_4_12_7_1_2439 95 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 155 254 (accept_3_2 94 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 155 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 155 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 92 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 155 254 (accept_3_2 91 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 155 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 155 254 (accept_3_2 88 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 155 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 155 254
  (Polychromatic418967fa.accept_10_6_5_4_1_571 86 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 155 254 (accept_3_2 85 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 155 254 (Polychromatic418967fa.accept_13_6_12_7_1_5131 84 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 155 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 155 254 (accept_3_2 82 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 155 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 155 254 (accept_3_2 79 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 155 254 (Polychromatic418967fa.accept_14_8_1_2_1_965 78 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 254 (accept_3_2 76 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 155 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 155 254
  (Polychromatic418967fa.accept_22_8_1_12_1_7506 74 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 155 254 (accept_3_2 73 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 155 254 (Polychromatic418967fa.accept_19_15_3_7_1_5875 72 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 155 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 71 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 254 (accept_3_2 70 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 155 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 155 254 (accept_3_2 67 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 155 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 254 (accept_3_2 64 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 254 (accept_3_2 61 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 155 254 (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 155 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 254 (accept_3_2 58 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 254
  (Polychromatic418967fa.accept_10_6_5_4_1_571 56 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 155 254 (accept_3_2 55 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 155 254 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 254 (accept_3_2 52 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 254
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 50 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 155 254 (accept_3_2 49 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 155 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 155 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 254 (Polychromatic418967fa.accept_13_8_12_7_1_2442 47 155
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 254 (accept_3_2 46 155
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 254 (accept_3_2 43 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 254 (Polychromatic418967fa.accept_17_8_2_16_1_5598 42 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 254 (accept_3_2 40 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 254 (accept_3_2 37 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 254 (Polychromatic418967fa.accept_16_3_11_14_1_446 35 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 254 (accept_3_2 34 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 155 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 254 (accept_3_2 31 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 254 (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 254 (accept_3_2 28 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 254
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 254 (accept_3_2 25 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 254 (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 254 (accept_3_2 22 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 254 (accept_3_2 19 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 254 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 254 (accept_3_2 16 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 254
  (Polychromatic418967fa.accept_17_14_2_16_1_4380 14 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 155 254 (accept_3_2 13 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 155 254 (Polychromatic418967fa.accept_19_12_3_7_1_5832 12 155 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 155
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 254 (accept_3_2 10 155
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3
  9 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 254 (accept_3_2 7 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 254 (accept_3_2 4 155 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 254
  (Polychromatic418967fa.accept_15_2_5_14_1_61 2 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 254 (accept_3_2 1 155 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 154 254 (Eq.refl Bool.true) (allA_of_3_0 101 154 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 153
  254 (Eq.refl Bool.true) (allA_succ_of_accept 101 153 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 153 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 254 (accept_3_2 100 153 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99
  153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 153 254
  (Polychromatic418967fa.accept_21_14_6_2_1_4793 98 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 153 254 (accept_3_2 97 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 153 254 (Polychromatic418967fa.accept_18_6_9_2_1_1575 96 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 153 254 (accept_3_2 94 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 153 254 (Polychromatic418967fa.accept_18_3_9_2_1_5053 93 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 153 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 92 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 153 254 (accept_3_2 91 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 153 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 153 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 254 (accept_3_2 88 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 153 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 86 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 153 254 (accept_3_2 85 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 153 254 (Polychromatic418967fa.accept_16_4_9_14_1_3883 84 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 254 (accept_3_2 82 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 153 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 153 254 (accept_3_2 79 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 153 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 153 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 254 (accept_3_2 76 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 153 254 (accept_3_2 73 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 153 254 (Polychromatic418967fa.accept_21_9_6_2_1_3357 72 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 254 (accept_3_2 70 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 254 (Polychromatic418967fa.accept_10_9_3_4_1_985 69 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 254
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 68 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 254 (accept_3_2 67 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 153 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 153 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 254 (accept_3_2 64 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 254
  (Polychromatic418967fa.accept_15_2_3_14_1_972 62 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 254 (accept_3_2 61 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 254 (accept_3_2 58 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 254
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 56 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 254 (accept_3_2 55 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 254 (accept_3_2 52 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 254 (accept_3_2 49 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 153 254 (Polychromatic418967fa.accept_19_10_1_7_1_10040 48 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 254 (accept_3_2 46 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 254
  (Polychromatic418967fa.accept_19_6_1_7_1_5872 44 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 254 (accept_3_2 43 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 153 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 153 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 254 (accept_3_2 40 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 254 (accept_3_2 37 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 153 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 254 (accept_3_2 34 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 254 (Polychromatic418967fa.accept_21_12_6_2_1_7950 33 153 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 254 (accept_3_2 31 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 153 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 153 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 254 (accept_3_2 28 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 254
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 254 (accept_3_2 25 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 153 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 254 (accept_3_2 22 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 254 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 153 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 254 (accept_3_2 19 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 254 (accept_3_2 16 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 254
  (Polychromatic418967fa.accept_21_14_6_2_1_4793 14 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 254 (accept_3_2 13 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 254 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 254 (accept_3_2 10 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 254 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 254 (accept_3_2 7 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 254 (accept_3_2 4 153 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 254
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 254 (accept_3_2 1 153 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 152 254 (Eq.refl Bool.true) (allA_succ_of_gcd 102 152 254 2 51 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 152 254 (Polychromatic418967fa.accept_7_3_5_2_1_17
  101 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 152 254 2 50 76 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 152 254
  (Polychromatic418967fa.accept_13_8_9_7_1_530 99 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 152 254 2 49 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 152 254 (accept_3_2 97 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 152 254 2 48 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 152 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 152 254 2 47 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 152 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 93 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 152 254 2 46 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 152 254 (accept_3_2 91 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 152 254 2 45 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 152 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 152 254 2 44 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 152 254 2 43 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 152 254 (accept_3_2 85 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 152 254 2 42 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 152 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 83 152 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 254 2 41 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 254 2 40 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 254 (accept_3_2 79 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 254 2 39 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 254 2 38 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 152 254 2 37 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 152 254 (accept_3_2 73 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 254 2 36 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 152 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 152 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 254 2 35 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 254 2 34 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 254 (accept_3_2 67 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 254 2 33 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 254 (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 152 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 254 2 32 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 254
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 254 2 31 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 254 (accept_3_2 61 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 254 2 30 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 254 2 29 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 254 2 28 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 254 (accept_3_2 55 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 254 2 27 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 254 2 26 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 254 2 25 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 254 (accept_3_2 49 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 254 2 24 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 254 2 23 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 254 2 22 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 254 (accept_3_2 43 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 254 2 21 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 254 2 20 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 254 2 19 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 254 (accept_3_2 37 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 254 2 18 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 152 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 254 2 17 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 254 2 16 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 254 (accept_3_2 31 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 254 2 15 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 254 2 14 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 254 2 13 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 254 (accept_3_2 25 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 254 2 12 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 254 2 11 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 254 2 10 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 254 (accept_3_2 19 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 254 2 9 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 254 2 8 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 254 2 7 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 254 (accept_3_2 13 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 254 2 6 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 152 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 152 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 254 2 5 76 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 254
  (Polychromatic418967fa.accept_22_9_20_12_1_12407 9 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 152 254 2 4 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 152 254 (accept_3_2 7 152 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 152 254 2 3 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 152 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 254 2 2 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3
  152 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 254 2 1 76 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 254 (accept_3_2 1
  152 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 151 254 (Eq.refl Bool.true) (allA_of_3_0 104 151 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 150
  254 (Eq.refl Bool.true) (allA_succ_of_gcd 104 150 254 2 52 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 150 254 (accept_3_2 103 150 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 150 254 2 51 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 150 254 (Polychromatic418967fa.accept_20_1_10_14_1_1472 101 150 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 150 254 2 50 75 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 150 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 99 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 150 254 2 49 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 150 254 (accept_3_2 97 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 150 254 2 48 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 150 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 95 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 150 254 2 47 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 150 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 93 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 150 254 2 46 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 150 254 (accept_3_2 91 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 150 254 2 45 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 150 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 150 254 2 44 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 150 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 87 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 150 254 2 43 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 150 254 (accept_3_2 85 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 150 254 2 42 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 150 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 150 254 2 41 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 150 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 150 254 2 40 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 150 254 (accept_3_2 79 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 254 2 39 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 254 2 38 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 150 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 150 254 2 37 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 150 254 (accept_3_2 73 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 254 2 36 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 254 2 35 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 150 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 150 254 2 34 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 150 254 (accept_3_2 67 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 254 2 33 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 254 (Polychromatic418967fa.accept_20_5_10_14_1_5317 65 150 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 150 254 2 32 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 254 2 31 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 254 (accept_3_2 61 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 254 2 30 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 254 2 29 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 254 2 28 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 150 254 (accept_3_2 55 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 254 2 27 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 254 2 26 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 254 2 25 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 254 (accept_3_2 49 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 254 2 24 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 254 2 23 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 150 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 150 254 2 22 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 150 254 (accept_3_2 43 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 254 2 21 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 254 2 20 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 254 2 19 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 254 (accept_3_2 37 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 254 2 18 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 254 2 17 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 254 2 16 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 254 (accept_3_2 31 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 254 2 15 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 254 2 14 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 254 2 13 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 254 (accept_3_2 25 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 254 2 12 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 254 2 11 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 254 2 10 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 254 (accept_3_2 19 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 254 2 9 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 150 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 254 2 8 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 254 2 7 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 254 (accept_3_2 13 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 254 2 6 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 254 (Polychromatic418967fa.accept_17_11_14_16_1_1270 11 150 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 254 2 5 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 254 2 4 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 254 (accept_3_2 7 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  254 2 3 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  150 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 150 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 254 2 2 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 150 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 150 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 254 2 1 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 254 (accept_3_2 1 150 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 149 254 (Eq.refl Bool.true) (allA_succ_of_accept 105 149 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 105 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 149 254 (Polychromatic418967fa.accept_11_5_6_1_1_988 104 149 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 149 254 (accept_3_2 103 149 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 149 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 149 254
  (Polychromatic418967fa.accept_19_6_16_7_1_11433 101 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 149 254 (accept_3_2 100 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 149 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 149 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 149 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 149 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 149 254 (accept_3_2 97 149 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 149 254 (Polychromatic418967fa.accept_9_6_5_2_1_421
  96 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 149 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 149 254 (accept_3_2 94 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 149 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 149 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 92 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 149 254 (accept_3_2 91 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 149 254 (Polychromatic418967fa.accept_13_12_6_7_1_1071 90 149
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 149 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 89 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 149 254 (accept_3_2 88 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 149 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 149 254 (Polychromatic418967fa.accept_19_10_16_7_1_10039 86 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 254 (accept_3_2 85 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 149 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 149 254 (accept_3_2 82 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 149 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 149 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 254 (accept_3_2 79 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 254
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 77 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 149 254 (accept_3_2 76 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 149 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 149 254 (Polychromatic418967fa.accept_13_9_6_7_1_551 74 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 254 (accept_3_2 73 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 254 (Polychromatic418967fa.accept_22_6_17_12_1_7704 72 149
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 149 254 (accept_3_2 70 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 149 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 149 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 68 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 254 (accept_3_2 67 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 149 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 254
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 65 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 254 (accept_3_2 64 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 254 (accept_3_2 61 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 254 (accept_3_2 58 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 254 (accept_3_2 55 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 254 (Polychromatic418967fa.accept_17_3_13_16_1_2183 54 149
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 149 254 (accept_3_2 52 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 149 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 149 254 (Polychromatic418967fa.accept_19_12_16_7_1_4456 50 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 254 (accept_3_2 49 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 149 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 254 (accept_3_2 46 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 149 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 254 (accept_3_2 43 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 254
  (Polychromatic418967fa.accept_16_9_5_14_1_6126 41 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 254 (accept_3_2 40 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 254 (accept_3_2 37 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 254 (Polychromatic418967fa.accept_19_17_16_7_1_7213 36 149
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 254 (accept_3_2 34 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 254 (accept_3_2 31 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 149 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 254
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 254 (accept_3_2 28 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 254 (accept_3_2 25 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 254 (accept_3_2 22 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 254 (accept_3_2 19 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 149
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 254 (accept_3_2 16 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 254 (Polychromatic418967fa.accept_13_1_6_7_1_550 14 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 254 (accept_3_2 13 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 149 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 254 (accept_3_2 10 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 254 (accept_3_2 7 149 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 254
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 254 (accept_3_2 4 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 254 (Polychromatic418967fa.accept_19_2_16_7_1_11424 2 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 254 (accept_3_2 1 149 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 149
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 148 254 (Eq.refl Bool.true) (allA_of_3_0 107 148 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 147 254 (Eq.refl Bool.true) (allA_succ_of_accept 107 147 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 147 254 (accept_3_2 106 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 147 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 147 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 104 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 254 (accept_3_2 103 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 147 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 102 147
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 147 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 147 254 (accept_3_2 100 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 147 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 99 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 147 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 147 254 (accept_3_2 97 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 147 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 147 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 147 254 (accept_3_2 94 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 147 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 147 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 92 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 254 (accept_3_2 91 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 147 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 90 147
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 147 254 (accept_3_2 88 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 147 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 147 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 254 (accept_3_2 85 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 147 254 (Polychromatic418967fa.accept_13_6_4_7_1_2464 84 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 147 254 (accept_3_2 82 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 147 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 147 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 254 (accept_3_2 79 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 147 254 (accept_3_2 76 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 147 254 (Polychromatic418967fa.accept_13_10_4_7_1_2465 75 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 147 254 (Polychromatic418967fa.accept_11_8_4_1_1_1000 74 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 254 (accept_3_2 73 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 147
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 254 (accept_3_2 70 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 147 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 147 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 254 (accept_3_2 67 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 254 (accept_3_2 64 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 147 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 254 (accept_3_2 61 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 254 (accept_3_2 58 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 147 254 (Polychromatic418967fa.accept_15_11_12_14_1_2612 56 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 254 (accept_3_2 55 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 147
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 254 (accept_3_2 52 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 254 (accept_3_2 49 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 254 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 254 (accept_3_2 46 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 254 (accept_3_2 43 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 254 (accept_3_2 40 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 254 (Polychromatic418967fa.accept_13_12_4_7_1_2520 38 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 254 (accept_3_2 37 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 254 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 147
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 254 (accept_3_2 34 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 254 (accept_3_2 31 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 254 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 254 (accept_3_2 28 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 254 (Polychromatic418967fa.accept_16_11_3_14_1_5043 27 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 254 (accept_3_2 25 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 254 (accept_3_2 22 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 254 (Polychromatic418967fa.accept_25_20_22_4_1_15523 20 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 254 (accept_3_2 19 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 147
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 254 (accept_3_2 16 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 254 (accept_3_2 13 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 254 (accept_3_2 10 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 254 (accept_3_2 7 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 147 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 254 (accept_3_2 4 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 147 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 254 (accept_3_2 1 147 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 146 254 (Eq.refl Bool.true) (allA_succ_of_gcd 108 146 254 2 54 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 146 254
  (Polychromatic418967fa.accept_25_7_21_4_1_15522 107 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 146 254 2 53 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 146 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 105 146 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 146 254 2 52 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 146 254 (accept_3_2 103 146 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 146 254 2 51 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 146 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 101 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 146 254 2 50 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 146 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 99 146 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 146 254 2 49 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 146 254 (accept_3_2 97 146 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 146 254 2 48 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 146 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 95
  146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 146 254 2 47 73 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 146 254
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 93 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 146 254 2 46 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 146 254 (accept_3_2 91 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 146 254 2 45 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 146 254 (Polychromatic418967fa.accept_13_11_3_7_1_2513 89 146 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 254 2 44 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 87 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 254 2 43 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 254 (accept_3_2 85 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 254 2 42 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 254 (Polychromatic418967fa.accept_22_17_14_12_1_12335 83 146 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 254 2 41 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 254 2 40 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 254 (accept_3_2 79 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 254 2 39 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 254 (Polychromatic418967fa.accept_17_9_10_16_1_3217 77 146 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 254 2 38 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 75 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 254 2 37 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 254 (accept_3_2 73 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 254 2 36 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 146 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 254 2 35 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 254
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 69 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 254 2 34 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 254 (accept_3_2 67 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 254 2 33 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 146 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 254 2 32 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 254
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 146 254 2 31 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 146 254 (accept_3_2 61 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 254 2 30 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 146 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 254 2 29 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 254 2 28 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 254 (accept_3_2 55 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 254 2 27 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 146 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 254 2 26 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 254
  (Polychromatic418967fa.accept_20_11_6_14_1_2621 51 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 146 254 2 25 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 146 254 (accept_3_2 49 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 254 2 24 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 254 (Polychromatic418967fa.accept_13_8_3_7_1_2455 47 146 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 254 2 23 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 254 2 22 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 254 (accept_3_2 43 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 254 2 21 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 254 (Polychromatic418967fa.accept_17_7_10_16_1_5582 41 146 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 254 2 20 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 254 2 19 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 254 (accept_3_2 37 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 254 2 18 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 146 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 254 2 17 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 254
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 33 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 146 254 2 16 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 146 254 (accept_3_2 31 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 254 2 15 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 146 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 254 2 14 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 254
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 254 2 13 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 254 (accept_3_2 25 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 254 2 12 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 254 (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 146 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 254 2 11 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 254
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 254 2 10 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 254 (accept_3_2 19 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 254 2 9 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 146 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 254 2 8 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 254 2 7 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 254 (accept_3_2 13 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 254 2 6 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 146 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 254 2 5 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 254
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 254 2 4 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 254 (accept_3_2 7 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  254 2 3 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 146 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 254 2 2 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 146 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 254 2 1 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 254 (accept_3_2 1 146 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 145 254 (Eq.refl Bool.true) (allA_of_3_0 110 145 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 144 254 (Eq.refl Bool.true) (allA_succ_of_gcd 110 144 254 2 55 72 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 144 254 (accept_3_2 109 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 144 254 2 54 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 144 254 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  107 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 144 254 2 53 72 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 144 254
  (Polychromatic418967fa.accept_28_21_4_2_1_15521 105 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 144 254 2 52 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 144 254 (accept_3_2 103 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 144 254 2 51 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 144 254 (Polychromatic418967fa.accept_25_1_19_4_1_8396 101 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 144 254 2 50 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 144 254
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 99 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 144 254 2 49 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 144 254 (accept_3_2 97 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 144 254 2 48 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 144 254 (Polychromatic418967fa.accept_15_5_9_14_1_1724 95 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 144 254 2 47 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 144 254
  (Polychromatic418967fa.accept_14_9_4_2_1_983 93 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 144 254 2 46 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 144 254 (accept_3_2 91 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 144 254 2 45 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 144 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 144 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 144 254 2 44 72 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 144 254
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 87 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 144 254 2 43 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 144 254 (accept_3_2 85 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 254 2 42 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 144 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 254 2 41 72 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 144 254
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 144 254 2 40 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 144 254 (accept_3_2 79 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 254 2 39 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 254 (Polychromatic418967fa.accept_17_9_8_16_1_2176 77 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 254 2 38 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 144 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 144 254 2 37 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 144 254 (accept_3_2 73 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 254 2 36 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 254 (Polychromatic418967fa.accept_13_6_1_7_1_1690 71 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 254 2 35 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 144 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 144 254 2 34 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 144 254 (accept_3_2 67 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 254 2 33 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 254 (Polychromatic418967fa.accept_14_9_4_2_1_983 65 144 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 254 2 32 72 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 254
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 144 254 2 31 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 144 254 (accept_3_2 61 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 254 2 30 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 254 (Polychromatic418967fa.accept_20_19_4_14_1_8345 59 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 254 2 29 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 254
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 144 254 2 28 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 144 254 (accept_3_2 55 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 254 2 27 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 254 (Polychromatic418967fa.accept_15_8_9_14_1_4577 53 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 254 2 26 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 254
  (Polychromatic418967fa.accept_14_9_4_2_1_983 51 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 144 254 2 25 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 144 254 (accept_3_2 49 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 254 2 24 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 144 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 254 2 23 72 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 254
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 254 2 22 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 254 (accept_3_2 43 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 254 2 21 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 144 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 254 2 20 72 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 254
  (Polychromatic418967fa.accept_20_19_4_14_1_8345 39 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 144 254 2 19 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 144 254 (accept_3_2 37 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 254 2 18 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 254 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 254 2 17 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 254 2 16 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 144 254 (accept_3_2 31 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 254 2 15 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 254 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 254 2 14 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 254 2 13 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 254 (accept_3_2 25 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 254 2 12 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 254 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 144 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 254 2 11 72 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 254
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 254 2 10 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 144 254 (accept_3_2 19 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 254 2 9 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 254 (Polychromatic418967fa.accept_31_17_20_6_1_15520 17 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 254 2 8 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 254
  (Polychromatic418967fa.accept_19_15_11_7_1_8711 15 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 254 2 7 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 254 (accept_3_2 13 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 254 2 6 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 254 (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 254 2 5 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 254
  (Polychromatic418967fa.accept_14_9_4_2_1_983 9 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 254 2 4 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 254 (accept_3_2 7 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144
  254 2 3 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 144 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 254 2 2 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 144 254 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 144 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 254 2 1 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 254 (accept_3_2 1 144 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 143 254 (Eq.refl Bool.true) (allA_succ_of_accept 111 143 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 111 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 143 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 110 143 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 143 254 (accept_3_2 109 143 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 143 254 (Polychromatic418967fa.accept_17_6_7_16_1_6836 108 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 143 254
  (Polychromatic418967fa.accept_10_7_3_4_1_978 107 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 143 254 (accept_3_2 106 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 143 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 143 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 104 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 143 254 (accept_3_2 103 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 143 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 102 143
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 143 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 143 254 (accept_3_2 100 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 143 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 143 254 (Polychromatic418967fa.accept_18_8_17_2_1_1557 98 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 143 254 (accept_3_2 97 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 143 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 143 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 143 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 95 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 143 254 (accept_3_2 94 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 143 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 143 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 254 (accept_3_2 91 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 143 254 (accept_3_2 88 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 143 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 143 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 254 (accept_3_2 85 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 143 254 (accept_3_2 82 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 143 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 143 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 254 (accept_3_2 79 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 143 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 143 254 (accept_3_2 76 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 143 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 143 254 (Polychromatic418967fa.accept_16_10_15_14_1_1086 74 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 254 (accept_3_2 73 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 254 (Polychromatic418967fa.accept_21_9_17_2_1_9537 72 143
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 143 254 (accept_3_2 70 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 143 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 143 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 254 (accept_3_2 67 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 143 254 (accept_3_2 64 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 143 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 143 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 254 (accept_3_2 61 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 254 (accept_3_2 58 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 254 (accept_3_2 55 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 143 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 254 (accept_3_2 52 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 254 (accept_3_2 49 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 254 (accept_3_2 46 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 254 (accept_3_2 43 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 143 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 254 (accept_3_2 40 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 254 (Polychromatic418967fa.accept_30_8_23_14_1_15519 38 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 254 (accept_3_2 37 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 143 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 254
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 254 (accept_3_2 34 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 254 (accept_3_2 31 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 254 (accept_3_2 28 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 254 (accept_3_2 25 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 254 (accept_3_2 22 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 254 (accept_3_2 19 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 254 (Polychromatic418967fa.accept_19_18_10_7_1_3174 18 143 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 254 (accept_3_2 16 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 254 (accept_3_2 13 143 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 254
  (Polychromatic418967fa.accept_18_11_17_2_1_6349 11 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 143 254 (accept_3_2 10 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 143 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 143 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 254 (accept_3_2 7 143 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 254 (accept_3_2 4 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 254 (Polychromatic418967fa.accept_25_2_18_4_1_15518 2 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 254 (accept_3_2 1 143 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 143
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 142 254 (Eq.refl Bool.true) (allA_of_3_0 113 142 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 141 254 (Eq.refl Bool.true) (allA_succ_of_accept 113 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 141 254 (accept_3_2 112 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 141 254 (Polychromatic418967fa.accept_15_5_6_14_1_1721 110 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 254 (accept_3_2 109 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 141 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 108 141
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 141 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 141 254 (accept_3_2 106 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 141 254 (Polychromatic418967fa.accept_10_5_1_4_1_1444 105 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 141 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 104 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 254 (accept_3_2 103 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 141 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 141
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 141 254 (accept_3_2 100 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 141 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 254 (accept_3_2 97 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 254 (Polychromatic418967fa.accept_13_5_11_7_1_559 96 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 141 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 141 254 (accept_3_2 94 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 141 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 141 254 (Polychromatic418967fa.accept_13_1_11_7_1_1704 92 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 254 (accept_3_2 91 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 141 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 141 254 (accept_3_2 88 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 141 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 254 (accept_3_2 85 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 254 (accept_3_2 82 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 141 254 (Polychromatic418967fa.accept_13_3_11_7_1_2488 81 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 141 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 80 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 254 (accept_3_2 79 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 254 (accept_3_2 76 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 141 254 (Polychromatic418967fa.accept_13_9_11_7_1_1077 74 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 254 (accept_3_2 73 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 254 (Polychromatic418967fa.accept_17_4_5_16_1_3240 72 141
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 254 (accept_3_2 70 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 141 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 141 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 254 (accept_3_2 67 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 254 (accept_3_2 64 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 141 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 254 (accept_3_2 61 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 254 (Polychromatic418967fa.accept_21_18_15_2_1_4806 60 141 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 254 (accept_3_2 58 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 254 (Polychromatic418967fa.accept_13_4_11_7_1_558 56 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 254 (accept_3_2 55 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 254 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 141
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 254 (accept_3_2 52 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 254 (accept_3_2 49 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 254 (accept_3_2 46 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 254 (accept_3_2 43 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 254 (accept_3_2 40 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 254 (accept_3_2 37 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 254 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 254 (accept_3_2 34 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 254 (Polychromatic418967fa.accept_16_1_13_14_1_1064 33 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 254 (accept_3_2 31 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 254 (accept_3_2 28 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 254 (accept_3_2 25 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 254 (accept_3_2 22 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 254 (accept_3_2 19 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 254 (accept_3_2 16 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 254 (accept_3_2 13 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 254 (accept_3_2 10 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 254 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 254 (accept_3_2 7 141 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 254 (accept_3_2 4 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 254 (Polychromatic418967fa.accept_17_2_5_16_1_1264 2 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 254 (accept_3_2 1 141 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 140 254 (Eq.refl Bool.true) (allA_succ_of_gcd 114 140 254 2 57 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 140 254
  (Polychromatic418967fa.accept_12_5_8_2_1_309 113 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 140 254 2 56 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 140 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 111 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 140 254 2 55 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 140 254 (accept_3_2 109 140 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 140 254 2 54 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 140 254 (Polychromatic418967fa.accept_9_8_5_2_1_422
  107 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 140 254 2 53 70 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 140 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 105 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 140 254 2 52 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 140 254 (accept_3_2 103 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 140 254 2 51 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 140 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 101 140 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 140 254 2 50 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 140 254
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 99 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 140 254 2 49 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 140 254 (accept_3_2 97 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 140 254 2 48 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 140 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 95 140 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 140 254 2 47 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 140 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 93 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 140 254 2 46 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 140 254 (accept_3_2 91 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 140 254 2 45 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 140 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 140 254 2 44 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 140 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 140 254 2 43 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 140 254 (accept_3_2 85 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 140 254 2 42 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 140 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 83 140 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 254 2 41 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 254
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 140 254 2 40 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 140 254 (accept_3_2 79 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 140 254 2 39 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 140 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 254 2 38 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 140 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 140 254 2 37 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 140 254 (accept_3_2 73 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 140 254 2 36 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 140 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 254 2 35 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 140 254 2 34 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 140 254 (accept_3_2 67 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 254 2 33 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 140 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 254 2 32 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 254
  (Polychromatic418967fa.accept_23_17_2_1_1_15517 63 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 140 254 2 31 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 140 254 (accept_3_2 61 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 254 2 30 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 254 (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 140 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 254 2 29 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 254 2 28 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 254 (accept_3_2 55 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 254 2 27 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 254 2 26 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 254 2 25 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 254 (accept_3_2 49 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 254 2 24 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 140 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 254 2 23 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 254
  (Polychromatic418967fa.accept_21_3_14_2_1_7978 45 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 140 254 2 22 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 140 254 (accept_3_2 43 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 254 2 21 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 254 2 20 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 254 2 19 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 254 (accept_3_2 37 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 254 2 18 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 140 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 254 2 17 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 140 254 2 16 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 140 254 (accept_3_2 31 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 254 2 15 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 254 2 14 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 254
  (Polychromatic418967fa.accept_21_6_14_2_1_7980 27 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 254 2 13 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 140 254 (accept_3_2 25 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 254 2 12 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 140 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 254 2 11 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 254 2 10 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 254 (accept_3_2 19 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 254 2 9 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 140 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 140 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 254 2 8 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 140 254 2 7 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 140 254 (accept_3_2 13 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 140 254 2 6 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 140 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 140 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 254 2 5 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 254
  (Polychromatic418967fa.accept_15_9_5_14_1_973 9 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 254 2 4 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 254 (accept_3_2 7 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  254 2 3 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  140 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 140 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 254 2 2 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 140 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 140 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 254 2 1 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 254 (accept_3_2 1 140 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 139 254 (Eq.refl Bool.true) (allA_of_3_0 116 139 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 117 138 254 (Eq.refl Bool.true) (allA_succ_of_gcd 116 138 254 2 58 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 138 254 (accept_3_2 115 138 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 138 254 2 57 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 138 254 (Polychromatic418967fa.accept_9_5_3_2_1_171
  113 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 138 254 2 56 69 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 138 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 111 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 138 254 2 55 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 138 254 (accept_3_2 109 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 138 254 2 54 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 138 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 107 138 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 138 254 2 53 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 138 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 105 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 138 254 2 52 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 138 254 (accept_3_2 103 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 138 254 2 51 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 138 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 101 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 138 254 2 50 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 138 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 99 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 138 254 2 49 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 138 254 (accept_3_2 97 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 138 254 2 48 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 138 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 138 254 2 47 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 138 254
  (Polychromatic418967fa.accept_11_5_6_1_1_988 93 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 138 254 2 46 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 138 254 (accept_3_2 91 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 254 2 45 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 138 254 2 44 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 138 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 138 254 2 43 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 138 254 (accept_3_2 85 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 254 2 42 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 254 (Polychromatic418967fa.accept_22_17_6_12_1_5923 83 138 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 254 2 41 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 138 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 138 254 2 40 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 254 (accept_3_2 79 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 254 2 39 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 254 2 38 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 138 254 2 37 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 254 (accept_3_2 73 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 254 2 36 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 254 2 35 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 138 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 138 254 2 34 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 254 (accept_3_2 67 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 254 2 33 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 254 (Polychromatic418967fa.accept_17_14_2_16_1_4380 65 138 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 254 2 32 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 254 2 31 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 254 (accept_3_2 61 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 254 2 30 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 254 2 29 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 254 2 28 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 254 (accept_3_2 55 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 254 2 27 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 254 2 26 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 254 2 25 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 254 (accept_3_2 49 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 254 2 24 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 254 (Polychromatic418967fa.accept_15_2_3_14_1_972 47 138 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 254 2 23 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 254 2 22 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 254 (accept_3_2 43 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 254 2 21 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 254 2 20 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 254 2 19 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 254 (accept_3_2 37 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 254 2 18 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 254 2 17 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 254 2 16 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 254 (accept_3_2 31 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 254 2 15 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 254 2 14 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 254
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 254 2 13 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 254 (accept_3_2 25 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 254 2 12 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 254 2 11 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 254 2 10 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 254 (accept_3_2 19 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 254 2 9 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 254 2 8 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 254 2 7 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 254 (accept_3_2 13 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 254 2 6 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 138 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 254 2 5 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 254 2 4 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 254 (accept_3_2 7 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  254 2 3 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 138 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 254 2 2 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 138 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 254 2 1 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 254 (accept_3_2 1 138 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 137 254 (Eq.refl Bool.true) (allA_succ_of_accept 117 137 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 117 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 137 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 116 137 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 137 254 (accept_3_2 115 137 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 137 254 (Polychromatic418967fa.accept_17_12_1_16_1_4360 114 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 137 254
  (Polychromatic418967fa.accept_10_3_7_4_1_584 113 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 137 254 (accept_3_2 112 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 137 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 110 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 137 254 (accept_3_2 109 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 137 254 (Polychromatic418967fa.accept_15_3_2_14_1_1713 108
  137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 137 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 137 254 (accept_3_2 106 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 137 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 137 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 104 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 137 254 (accept_3_2 103 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 137 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 102 137
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 137 254
  (Polychromatic418967fa.accept_10_1_7_4_1_968 101 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 137 254 (accept_3_2 100 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 137 254 (Polychromatic418967fa.accept_19_3_4_7_1_987 98 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 254 (accept_3_2 97 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 137 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 137 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 137 254 (accept_3_2 94 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 137 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 137 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 92 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 254 (accept_3_2 91 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 137 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 137 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 137 254 (accept_3_2 88 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 137 254 (Polychromatic418967fa.accept_18_14_11_2_1_5068 86 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 254 (accept_3_2 85 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 254 (Polychromatic418967fa.accept_16_4_9_14_1_3883 84 137
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 254 (accept_3_2 82 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 137 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 80 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 254 (accept_3_2 79 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 254 (Polychromatic418967fa.accept_15_3_2_14_1_1713 78 137
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 254
  (Polychromatic418967fa.accept_19_1_4_7_1_2018 77 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 137 254 (accept_3_2 76 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 137 254 (Polychromatic418967fa.accept_23_5_22_1_1_12148 74 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 254 (accept_3_2 73 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 137
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 137 254 (accept_3_2 70 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 137 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 137 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 137 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 254 (accept_3_2 67 137 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 254 (Polychromatic418967fa.accept_17_15_1_16_1_8166 66 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 254
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 65 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 254 (accept_3_2 64 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 137 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 254 (accept_3_2 61 137 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 254 (Polychromatic418967fa.accept_19_3_4_7_1_987 60 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 254 (accept_3_2 58 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 254 (accept_3_2 55 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 254
  (Polychromatic418967fa.accept_10_3_7_4_1_584 53 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 254 (accept_3_2 52 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 254 (accept_3_2 49 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 254 (accept_3_2 46 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 254 (accept_3_2 43 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 137
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 254 (accept_3_2 40 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 254 (Polychromatic418967fa.accept_21_17_11_2_1_7953 38 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 254 (accept_3_2 37 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 254 (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 137
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 254 (accept_3_2 34 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 254 (accept_3_2 31 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 254 (Polychromatic418967fa.accept_19_11_4_7_1_1029 30 137
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 254
  (Polychromatic418967fa.accept_17_12_1_16_1_4360 29 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 137 254 (accept_3_2 28 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 254 (accept_3_2 25 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 254
  (Polychromatic418967fa.accept_22_2_5_12_1_15516 24 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 254 (accept_3_2 22 137 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 254 (accept_3_2 19 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 254 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 254 (accept_3_2 16 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 254
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 137 254 (accept_3_2 13 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 137 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 254 (accept_3_2 10 137 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 254 (accept_3_2 7 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 254 (accept_3_2 4 137 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 254 (accept_3_2 1 137 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 136 254 (Eq.refl Bool.true) (allA_of_3_0 119 136 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 120 135 254 (Eq.refl Bool.true) (allA_succ_of_accept 119 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 135 254 (accept_3_2 118 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 135 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 116 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 135 254 (accept_3_2 115 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 135 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 114 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 113 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 135 254 (accept_3_2 112 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 135 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 111 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 135 254 (Polychromatic418967fa.accept_20_10_15_14_1_6797 110 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 135 254 (accept_3_2 109 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 135 254 (Polychromatic418967fa.accept_19_13_2_7_1_8738 108
  135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 135 254 (accept_3_2 106 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 135 254 (Polychromatic418967fa.accept_19_9_2_7_1_3149 104 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 254 (accept_3_2 103 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 135 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 102 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 135 254 (accept_3_2 100 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 135 254 (Polychromatic418967fa.accept_10_9_5_4_1_966 99 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 135 254 (Polychromatic418967fa.accept_21_14_9_2_1_8005 98 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 254 (accept_3_2 97 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 96 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 135 254 (accept_3_2 94 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 135 254 (Polychromatic418967fa.accept_19_16_2_7_1_11445 92 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 254 (accept_3_2 91 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 135 254 (accept_3_2 88 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 135 254 (Polychromatic418967fa.accept_21_3_9_2_1_6368 87 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 135 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 86 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 254 (accept_3_2 85 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 254 (Polychromatic418967fa.accept_16_4_7_14_1_3897 84 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 254 (accept_3_2 82 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 135 254 (Polychromatic418967fa.accept_13_2_5_7_1_1695 80 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 254 (accept_3_2 79 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 78 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 254 (accept_3_2 76 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 135 254 (Polychromatic418967fa.accept_18_3_9_2_1_5053 75 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 135 254 (Polychromatic418967fa.accept_14_4_9_2_1_95 74 135 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 254 (accept_3_2 73 135 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 254 (Polychromatic418967fa.accept_23_3_20_1_1_15515 72 135 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 135 254 (accept_3_2 70 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 135 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 68 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 254 (accept_3_2 67 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 135 254 (accept_3_2 64 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 135 254 (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 254 (Polychromatic418967fa.accept_19_5_2_7_1_1019 62 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 254 (accept_3_2 61 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 254 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 135 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 254 (accept_3_2 58 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 254 (accept_3_2 55 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 254 (accept_3_2 52 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 254 (Polychromatic418967fa.accept_13_11_5_7_1_2420 50 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 254 (accept_3_2 49 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 254 (Polychromatic418967fa.accept_20_8_15_14_1_1487 48 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 254 (accept_3_2 46 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 254 (Polychromatic418967fa.accept_23_21_20_1_1_15514 44 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 254 (accept_3_2 43 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 254 (accept_3_2 40 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 254 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 254 (Polychromatic418967fa.accept_13_12_5_7_1_1696 38 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 254 (accept_3_2 37 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 254 (accept_3_2 34 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 254 (Polychromatic418967fa.accept_14_4_9_2_1_95 32 135 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 254 (accept_3_2 31 135 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 254 (accept_3_2 28 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 254 (Polychromatic418967fa.accept_21_6_9_2_1_9554 27 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 254 (accept_3_2 25 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 254 (accept_3_2 22 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 254 (Polychromatic418967fa.accept_16_4_7_14_1_3897 20 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 254 (accept_3_2 19 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 254 (accept_3_2 16 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 254 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 254 (Polychromatic418967fa.accept_19_14_2_7_1_12841 14 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 254 (accept_3_2 13 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 254 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 135
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 254 (accept_3_2 10 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 254 (Polychromatic418967fa.accept_20_8_15_14_1_1487 8 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 254 (accept_3_2 7 135 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 135 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 254 (accept_3_2 4 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 254 (Polychromatic418967fa.accept_18_3_9_2_1_5053 3 135 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 135 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 254 (accept_3_2 1 135 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 134 254 (Eq.refl Bool.true) (allA_succ_of_gcd 120 134 254 2 60 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 134 254
  (Polychromatic418967fa.accept_21_14_8_2_1_11088 119 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 134 254 2 59 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 117 134 254 (Polychromatic418967fa.accept_23_2_19_1_1_15513 117 134 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 134 254 2 58 67 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 134 254 (accept_3_2
  115 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 134 254 2 57 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 134 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 113 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 134 254 2 56 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 134 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 111 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 134 254 2 55 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 134 254 (accept_3_2 109 134 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 134 254 2 54 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 134 254
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 107 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 134 254 2 53 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 134 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 105 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 134 254 2 52 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 134 254 (accept_3_2 103 134 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 134 254 2 51 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 134 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 101 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 134 254 2 50 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 134 254 (Polychromatic418967fa.accept_14_1_8_2_1_1675 99 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 134 254 2 49 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 134 254 (accept_3_2 97 134 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 134 254 2 48 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 134 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 95 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 134 254 2 47 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 134 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 93 134 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 134 254 2 46 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 134 254 (accept_3_2 91 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 134 254 2 45 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 134 254 (Polychromatic418967fa.accept_13_11_4_7_1_2419
  89 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 134 254 2 44 67 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 134 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 134 254 2 43 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 134 254 (accept_3_2 85 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 134 254 2 42 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 134 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 134 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 254 2 41 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 254
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 81 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 254 2 40 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 254 (accept_3_2 79 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 254 2 39 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 134 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 254 2 38 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 254 2 37 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 254 (accept_3_2 73 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 254 2 36 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 254 (Polychromatic418967fa.accept_13_6_4_7_1_2464 71 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 254 2 35 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 254 2 34 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 254 (accept_3_2 67 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 254 2 33 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 254 (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 254 2 32 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 254
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 63 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 134 254 2 31 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 134 254 (accept_3_2 61 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 254 2 30 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 134 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 254 2 29 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 254 2 28 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 254 (accept_3_2 55 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 254 2 27 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 254 (Polychromatic418967fa.accept_18_17_8_2_1_2622 53 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 254 2 26 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 254 2 25 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 254 (accept_3_2 49 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 254 2 24 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 134 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 254 2 23 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 254 2 22 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 254 (accept_3_2 43 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 254 2 21 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 134 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 254 2 20 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 254 2 19 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 254 (accept_3_2 37 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 254 2 18 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 254 (Polychromatic418967fa.accept_13_9_4_7_1_1694 35 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 254 2 17 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 254 2 16 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 254 (accept_3_2 31 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 254 2 15 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 254 (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 254 2 14 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 254 2 13 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 254 (accept_3_2 25 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 254 2 12 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 134 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 254 2 11 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 254 2 10 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 254 (accept_3_2 19 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 254 2 9 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 134 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 254 2 8 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 254 2 7 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 254 (accept_3_2 13 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 254 2 6 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 254 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 254 2 5 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 254
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 254 2 4 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 254 (accept_3_2 7 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  254 2 3 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 134 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 254 2 2 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 134 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 254 2 1 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 254 (accept_3_2 1 134 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 133 254 (Eq.refl Bool.true) (allA_of_3_0 122 133 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 123 132 254 (Eq.refl Bool.true) (allA_succ_of_gcd 122 132 254 2 61 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 132 254 (accept_3_2 121 132 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 132 254 2 60 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 132 254
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 119 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 132 254 2 59 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 117 132 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 117 132 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 132 254 2 58 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 132 254 (accept_3_2 115 132 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 132 254 2 57 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 132 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 113 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 132 254 2 56 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 132 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 111 132 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 132 254 2 55 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 132 254 (accept_3_2 109 132 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 254 2 54 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 107 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 132 254 2 53 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 132 254 (Polychromatic418967fa.accept_16_9_4_14_1_1878 105 132 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 132 254 2 52 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 254 (accept_3_2 103 132 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 132 254 2 51 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 132 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 101 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 132 254 2 50 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 132 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 99 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 132 254 2 49 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 254 (accept_3_2 97 132 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 132 254 2 48 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 132 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 95
  132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 132 254 2 47 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 132 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 93 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 132 254 2 46 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 132 254 (accept_3_2 91 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 254 2 45 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 89 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 132 254 2 44 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 132 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 87 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 132 254 2 43 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 132 254 (accept_3_2 85 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 254 2 42 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 254 (Polychromatic418967fa.accept_13_5_2_7_1_2414 83 132 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 254 2 41 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 254 2 40 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 254 (accept_3_2 79 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 254 2 39 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 254 2 38 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 254 2 37 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 254 (accept_3_2 73 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 254 2 36 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 254 2 35 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 254
  (Polychromatic418967fa.accept_15_9_12_14_1_963 69 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 132 254 2 34 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 132 254 (accept_3_2 67 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 254 2 33 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 254 (Polychromatic418967fa.accept_16_1_4_14_1_1896 65 132 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 254 2 32 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 254
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 63 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 132 254 2 31 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 132 254 (accept_3_2 61 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 254 2 30 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 254 2 29 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 254 2 28 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 254 (accept_3_2 55 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 254 2 27 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 254 2 26 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 254
  (Polychromatic418967fa.accept_21_9_6_2_1_3357 51 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 254 2 25 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 254 (accept_3_2 49 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 254 2 24 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 254 2 23 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 254 2 22 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 132 254 (accept_3_2 43 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 254 2 21 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 254 2 20 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 254 2 19 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 254 (accept_3_2 37 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 254 2 18 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 254 2 17 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 254
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 33 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 132 254 2 16 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 132 254 (accept_3_2 31 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 254 2 15 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 254 2 14 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 132 254 2 13 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 254 (accept_3_2 25 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 254 2 12 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 254 2 11 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 254 2 10 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 132 254 (accept_3_2 19 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 254 2 9 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 132 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 254 2 8 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 132 254 2 7 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 132 254 (accept_3_2 13 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 254 2 6 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 132 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 132 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 254 2 5 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 254
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 254 2 4 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 254 (accept_3_2 7 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132
  254 2 3 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  132 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 132 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 254 2 2 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 132 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 254 2 1 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 254 (accept_3_2 1 132 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 131 254 (Eq.refl Bool.true) (allA_succ_of_accept 123 131 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 123 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 131 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 122 131 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 131 254 (accept_3_2 121 131 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 131 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 120 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 131 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 119 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 131 254 (accept_3_2 118 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 131 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 116 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 131 254 (accept_3_2 115 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 131 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 114 131
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 131 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 113 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 131 254 (accept_3_2 112 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 131 254 (Polychromatic418967fa.accept_13_6_1_7_1_1690 110 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 131 254 (accept_3_2 109 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 131 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 108 131
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 131 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 107 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 131 254 (accept_3_2 106 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 131 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 104 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 131 254 (accept_3_2 103 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 131 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 102 131
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 131 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 131 254 (accept_3_2 100 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 131 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 131 254 (accept_3_2 97 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 131 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 131 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 95 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 131 254 (accept_3_2 94 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 131 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 92 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 254 (accept_3_2 91 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 131 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 131
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 131 254 (accept_3_2 88 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 131 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 86 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 254 (accept_3_2 85 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 131 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 254
  (Polychromatic418967fa.accept_20_3_11_14_1_5319 83 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 131 254 (accept_3_2 82 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 131 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 131 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 254 (accept_3_2 79 131 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 254 (Polychromatic418967fa.accept_9_6_5_2_1_421
  78 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 131 254 (accept_3_2 76 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 131 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 254 (accept_3_2 73 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 254 (Polychromatic418967fa.accept_15_12_11_14_1_3464 72 131 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 131 254 (accept_3_2 70 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 131 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017 68 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 254 (accept_3_2 67 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 131 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 131 254 (accept_3_2 64 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 254 (accept_3_2 61 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 254 (accept_3_2 58 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 254 (accept_3_2 55 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 254 (Polychromatic418967fa.accept_19_16_17_7_1_5845 54 131
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 254 (accept_3_2 52 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 254 (Polychromatic418967fa.accept_13_11_1_7_1_1691 50 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 254 (accept_3_2 49 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 131 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 254
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 254 (accept_3_2 46 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 254 (accept_3_2 43 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 254 (accept_3_2 40 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 254 (accept_3_2 37 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 254 (Polychromatic418967fa.accept_25_11_6_4_1_15512 36 131 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 254 (accept_3_2 34 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 254 (accept_3_2 31 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 254 (accept_3_2 28 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 254 (accept_3_2 25 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 254
  (Polychromatic418967fa.accept_20_3_11_14_1_5319 23 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 131 254 (accept_3_2 22 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 131
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 254 (accept_3_2 19 131
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 254 (accept_3_2 16 131 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 254
  (Polychromatic418967fa.accept_27_14_23_11_1_11701 14 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 254 (accept_3_2 13 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 254 (accept_3_2 10 131 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 254 (accept_3_2 7 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 254 (accept_3_2 4 131 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 254
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 254 (accept_3_2 1 131 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 130 254 (Eq.refl Bool.true) (allA_of_3_0 125 130 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 126 129 254 (Eq.refl Bool.true) (allA_succ_of_accept 125 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 129 254 (accept_3_2 124 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 123 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 129 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 122 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 129 254 (accept_3_2 121 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 129 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 120 129
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 119 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 129 254 (accept_3_2 118 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 129 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 117 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 129 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 116 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 254 (accept_3_2 115 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 129 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 114 129
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 129 254 (accept_3_2 112 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 129 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 110 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 254 (accept_3_2 109 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 108 129
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 129 254 (accept_3_2 106 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 129 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 129 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 104 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 254 (accept_3_2 103 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 102 129
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 129 254 (accept_3_2 100 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 129 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 254 (accept_3_2 97 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 254 (accept_3_2 94 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 129 254 (Polychromatic418967fa.accept_10_3_9_4_1_960 93 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 129 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 254 (accept_3_2 91 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 254 (accept_3_2 88 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 129 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 254 (accept_3_2 85 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 254 (Polychromatic418967fa.accept_13_6_12_7_1_5131 84 129 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 129 254 (accept_3_2 82 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 129 254 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 129 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 254 (accept_3_2 79 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 254 (accept_3_2 76 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 129 254 (Polychromatic418967fa.accept_17_6_10_16_1_9453 74 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 254 (accept_3_2 73 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 254 (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 129
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 254 (accept_3_2 70 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 129 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 129 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 254 (accept_3_2 67 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 254 (accept_3_2 64 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 129 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 254 (accept_3_2 61 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 254 (accept_3_2 58 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 129 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 129 254 (Polychromatic418967fa.accept_13_4_12_7_1_2439 56 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 254 (accept_3_2 55 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 129 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 254 (accept_3_2 52 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 254 (accept_3_2 49 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 254 (accept_3_2 46 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 254 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 254 (accept_3_2 43 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 254 (accept_3_2 40 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 254 (accept_3_2 37 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 129 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 254 (accept_3_2 34 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 254 (accept_3_2 31 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 254 (accept_3_2 28 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 254 (accept_3_2 25 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 254 (accept_3_2 22 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 254 (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 254 (accept_3_2 19 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 254 (accept_3_2 16 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 254 (accept_3_2 13 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 254 (accept_3_2 10 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 254 (Polychromatic418967fa.accept_17_9_10_16_1_3217 9 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 254 (accept_3_2 7 129 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 254 (accept_3_2 4 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 254 (Polychromatic418967fa.accept_22_2_19_12_1_7598 2 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 254 (accept_3_2 1 129 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 128 254 (Eq.refl Bool.true) (allA_succ_of_gcd 126 128 254 2 63 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 128 254
  (Polychromatic418967fa.accept_12_5_8_2_1_309 125 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 128 254 2 62 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 128 254 (Polychromatic418967fa.accept_20_3_8_14_1_5342 123 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 128 254 2 61 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 128 254 (accept_3_2 121 128 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 128 254 2 60 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 128 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 119 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 128 254 2 59 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 128 254 (Polychromatic418967fa.accept_19_3_14_7_1_7204 117 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 128 254 2 58 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 128 254 (accept_3_2 115 128 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 128 254 2 57 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 128 254
  (Polychromatic418967fa.accept_12_5_8_2_1_309 113 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 128 254 2 56 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 128 254 (Polychromatic418967fa.accept_15_6_8_14_1_4575 111 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 128 254 2 55 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 128 254 (accept_3_2 109 128 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 128 254 2 54 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 128 254
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 107 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 128 254 2 53 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 128 254 (Polychromatic418967fa.accept_11_6_7_1_1_564 105 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 128 254 2 52 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 128 254 (accept_3_2 103 128 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 128 254 2 51 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 128 254
  (Polychromatic418967fa.accept_12_5_8_2_1_309 101 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 128 254 2 50 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 128 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 99 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 128 254 2 49 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 128 254 (accept_3_2 97 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 128 254 2 48 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 128 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  95 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 128 254 2 47 64 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 128 254
  (Polychromatic418967fa.accept_17_8_9_16_1_6844 93 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 128 254 2 46 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 128 254 (accept_3_2 91 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 128 254 2 45 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 128 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 89 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 128 254 2 44 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 128 254
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 87 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 128 254 2 43 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 128 254 (accept_3_2 85 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 128 254 2 42 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 128 254 (Polychromatic418967fa.accept_11_6_7_1_1_564 83 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 254 2 41 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 254
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 81 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 128 254 2 40 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 128 254 (accept_3_2 79 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 128 254 2 39 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 128 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 254 2 38 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 254
  (Polychromatic418967fa.accept_19_18_14_7_1_5864 75 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 128 254 2 37 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 128 254 (accept_3_2 73 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 128 254 2 36 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 128 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 254 2 35 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 69 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 254 2 34 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 254 (accept_3_2 67 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 254 2 33 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 254 2 32 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 254
  (Polychromatic418967fa.accept_19_6_14_7_1_5902 63 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 128 254 2 31 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 254 (accept_3_2 61 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 254 2 30 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 254 2 29 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 254
  (Polychromatic418967fa.accept_13_5_11_7_1_559 57 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 254 2 28 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 254 (accept_3_2 55 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 254 2 27 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 254 2 26 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 254
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 128 254 2 25 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 128 254 (accept_3_2 49 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 254 2 24 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 254 2 23 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 254
  (Polychromatic418967fa.accept_20_5_8_14_1_5341 45 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 254 2 22 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 254 (accept_3_2 43 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 254 2 21 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 254 2 20 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 254 2 19 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 254 (accept_3_2 37 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 254 2 18 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 254 2 17 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 254
  (Polychromatic418967fa.accept_20_13_8_14_1_1467 33 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 128 254 2 16 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 128 254 (accept_3_2 31 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 254 2 15 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 254 2 14 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 254
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 254 2 13 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 254 (accept_3_2 25 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 254 2 12 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 254 2 11 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 254
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 254 2 10 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 254 (accept_3_2 19 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 254 2 9 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 128 254 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 128 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 254 2 8 64 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 254
  (Polychromatic418967fa.accept_19_15_14_7_1_2044 15 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 128 254 2 7 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 128 254 (accept_3_2 13 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 128 254 2 6 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 128 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 254 2 5 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 254 2 4 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 254 (accept_3_2 7 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  254 2 3 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 128 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 254 2 2 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 128 254 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 128 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 254 2 1 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 254 (accept_3_2 1 128 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 127 254 (allA_of_3_0 127 127 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 126 254
  (allA_succ_of_accept 125 126 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 125 126 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 126 254 2 62 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 126 254 (Polychromatic418967fa.accept_12_3_6_2_1_747
  123 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 126 254 2 61 63 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 126 254
  (accept_3_2 121 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 126 254 2 60 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 126 254
  (Polychromatic418967fa.accept_13_2_9_7_1_164 119 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 126 254 2 59 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 126 254 (Polychromatic418967fa.accept_12_9_6_2_1_1273 117 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 126 254 2 58 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 126 254 (accept_3_2 115 126 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 126 254 2 57 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 126 254
  (Polychromatic418967fa.accept_15_8_6_14_1_975 113 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 126 254 2 56 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 126 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 111 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 126 254 2 55 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 126 254 (accept_3_2 109 126 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 126 254 2 54 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 126 254
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 107 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 126 254 2 53 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 126 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 105 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 126 254 2 52 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 126 254 (accept_3_2 103 126 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 126 254 2 51 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 126 254
  (Polychromatic418967fa.accept_20_1_6_14_1_5312 101 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 126 254 2 50 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 126 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 99 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 126 254 2 49 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 126 254 (accept_3_2 97 126 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 126 254 2 48 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 126 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 95 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 126 254 2 47 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 126 254 (Polychromatic418967fa.accept_12_9_6_2_1_1273 93 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 126 254 2 46 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 126 254 (accept_3_2 91 126 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 126 254 2 45 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 126 254
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 89 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 126 254 2 44 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 126 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 87 126 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 126 254 2 43 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 254 (accept_3_2 85 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 126 254 2 42 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 254 (Polychromatic418967fa.accept_11_6_5_1_1_586
  83 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 254 2 41 63 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 254 2 40 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 254 (accept_3_2 79 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 254 2 39 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 254 (Polychromatic418967fa.accept_19_1_12_7_1_12723 77 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 254 2 38 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 75 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 254 2 37 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 254 (accept_3_2 73 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 254 2 36 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 254 (Polychromatic418967fa.accept_13_6_9_7_1_2430 71 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 254 2 35 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 254 2 34 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 254 (accept_3_2 67 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 254 2 33 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 126 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 254 2 32 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 126 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 126 254 2 31 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 254 (accept_3_2 61 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 254 2 30 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 254 (Polychromatic418967fa.accept_17_8_7_16_1_9508 59 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 254 2 29 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 254 2 28 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 254 (accept_3_2 55 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 254 2 27 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 254 (Polychromatic418967fa.accept_15_8_6_14_1_975 53 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 254 2 26 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 254 2 25 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 254 (accept_3_2 49 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 254 2 24 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 254 (Polychromatic418967fa.accept_13_8_9_7_1_530 47 126 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 254 2 23 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 254 2 22 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 254 (accept_3_2 43 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 254 2 21 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 254 (Polychromatic418967fa.accept_13_2_9_7_1_164 41 126 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 254 2 20 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 254
  (Polychromatic418967fa.accept_11_6_5_1_1_586 39 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 254 2 19 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 254 (accept_3_2 37 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 254 2 18 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 126 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 254 2 17 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 254 2 16 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 254 (accept_3_2 31 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 254 2 15 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 254 (Polychromatic418967fa.accept_13_3_9_7_1_1730 29 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 254 2 14 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 254 2 13 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 254 (accept_3_2 25 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 254 2 12 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 254 (Polychromatic418967fa.accept_15_8_6_14_1_975 23 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 254 2 11 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 254 2 10 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 254 (accept_3_2 19 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 254 2 9 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 126 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 254 2 8 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 254 2 7 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 254 (accept_3_2 13 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 254 2 6 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 254 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 254 2 5 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 254 2 4 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 254 (accept_3_2 7 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126
  254 2 3 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 126 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 254 2 2 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 126 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 126 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 254 2 1 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 254 (accept_3_2 1 126 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 254 (allA_succ_of_accept 124 125 254 (accept_3_2 124 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 123 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 125 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 122 125
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 125 254 (accept_3_2 121 125
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 125 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 120 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 119 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 125 254 (accept_3_2 118 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 125 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 125 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 125 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 116 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 125 254 (accept_3_2 115 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 125 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 114 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 125 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 113 125 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 254 (accept_3_2 112 125 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 125
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 125 254
  (Polychromatic418967fa.accept_19_15_11_7_1_8711 110 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 125 254 (accept_3_2 109 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 125 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 108 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 125
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 254 (accept_3_2 106 125
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 125 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 105 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 125 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 125 254 (accept_3_2 103 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 125 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 102 125 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 101 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 125 254 (accept_3_2 100 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 125 254 (Polychromatic418967fa.accept_15_8_5_14_1_986 98 125 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 254 (accept_3_2 97 125 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 125 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 125 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 125 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 125 254 (accept_3_2 94 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 125 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 125 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 92 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 254 (accept_3_2 91 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 254 (Polychromatic418967fa.accept_13_12_8_7_1_2526 90 125 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 125 254
  (Polychromatic418967fa.accept_10_9_5_4_1_966 89 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 254 (accept_3_2 88 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 125 254 (accept_3_2 85 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 125 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 125 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 254 (accept_3_2 82 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 125 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 125 254 (accept_3_2 79 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 125 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 254 (accept_3_2 76 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 125 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 254 (accept_3_2 73 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 125 254 (Polychromatic418967fa.accept_19_15_11_7_1_8711 72 125 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 125 254 (accept_3_2 70 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 125 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 125 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 254 (accept_3_2 67 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 125 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 254
  (Polychromatic418967fa.accept_16_1_13_14_1_1064 65 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 125 254 (accept_3_2 64 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 254 (Polychromatic418967fa.accept_13_10_8_7_1_1074 62 125
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 254 (accept_3_2 61 125
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 254 (accept_3_2 58 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 125 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 254 (Polychromatic418967fa.accept_10_6_5_4_1_571
  56 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 254 (accept_3_2 55
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 254
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 125 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 254 (accept_3_2 52 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 50
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 254 (accept_3_2 49
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 254 (accept_3_2 46 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 125 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 254 (Polychromatic418967fa.accept_12_8_5_2_1_746
  44 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 254 (accept_3_2 43
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 125 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 254 (accept_3_2 40 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 254 (accept_3_2 37
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 254 (accept_3_2 34 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 125 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 254 (Polychromatic418967fa.accept_7_4_6_2_1_451
  32 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 254 (accept_3_2 31
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 125 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 254 (accept_3_2 28 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 254 (Polychromatic418967fa.accept_10_6_5_4_1_571
  26 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 254 (accept_3_2 25
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 254 (accept_3_2 22 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 254 (Polychromatic418967fa.accept_12_8_5_2_1_746
  20 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 254 (accept_3_2 19
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 125 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 254 (accept_3_2 16 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 254 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 254 (accept_3_2 13
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 254 (accept_3_2 10 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 125 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 8
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 254 (accept_3_2 7 125
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 125 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 254 (accept_3_2 4 125 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 125 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 254 (Polychromatic418967fa.accept_13_2_8_7_1_2424
  2 125 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 254 (accept_3_2 1
  125 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 124 254 (allA_of_3_0 124 124 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 123 254
  (allA_succ_of_accept 122 123 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 122 123 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 123 254 (accept_3_2 121 123 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 123 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 120 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 123 254 (accept_3_2 118 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 123 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 116 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 123 254 (accept_3_2 115 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 114 123
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 113 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 123 254 (accept_3_2 112 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 123 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 111 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 123 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 110 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 254 (accept_3_2 109 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 254 (Polychromatic418967fa.accept_13_4_6_7_1_2471 108 123
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 123 254 (accept_3_2 106 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 123 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 104 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 254 (accept_3_2 103 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 123
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 123 254 (accept_3_2 100 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 123 254 (Polychromatic418967fa.accept_10_9_3_4_1_985 99 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 123 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 254 (accept_3_2 97 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 254 (accept_3_2 94 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 123 254 (Polychromatic418967fa.accept_13_1_6_7_1_550 92 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 254 (accept_3_2 91 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 123 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 254 (accept_3_2 88 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 254 (Polychromatic418967fa.accept_10_7_3_4_1_978 87 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 254 (accept_3_2 85 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 254 (accept_3_2 82 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 123 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 254 (accept_3_2 79 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 78 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 254 (accept_3_2 76 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 123 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 123 254 (Polychromatic418967fa.accept_13_9_6_7_1_551 74 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 254 (accept_3_2 73 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 254 (Polychromatic418967fa.accept_28_16_11_2_1_15511 72
  123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 254 (accept_3_2 70 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 123 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 254 (accept_3_2 67 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 254 (accept_3_2 64 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 254 (Polychromatic418967fa.accept_24_15_3_14_1_15510 63 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 254 (accept_3_2 61 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 254 (Polychromatic418967fa.accept_25_10_23_4_1_11892 60
  123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 254 (accept_3_2 58 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 254 (Polychromatic418967fa.accept_13_4_6_7_1_2471 56 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 254 (accept_3_2 55 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 123 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 254 (accept_3_2 52 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 254 (Polychromatic418967fa.accept_13_12_6_7_1_1071 51 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 254 (accept_3_2 49 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 254 (accept_3_2 46 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 254 (accept_3_2 43 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 254 (accept_3_2 40 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 254 (Polychromatic418967fa.accept_13_12_6_7_1_1071 38 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 254 (accept_3_2 37 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 123
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 254 (accept_3_2 34 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 254 (accept_3_2 31 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 254 (accept_3_2 28 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 254 (accept_3_2 25 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 254 (Polychromatic418967fa.accept_19_5_9_7_1_3137 24 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 254 (accept_3_2 22 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 254 (accept_3_2 19 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 254 (accept_3_2 16 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 254 (Polychromatic418967fa.accept_17_15_4_16_1_6890 15 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 254 (accept_3_2 13 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 254 (accept_3_2 10 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 254 (accept_3_2 7 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 123 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 254 (accept_3_2 4 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 123 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 254 (Polychromatic418967fa.accept_15_2_3_14_1_972 2 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 254 (accept_3_2 1 123 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_254_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


