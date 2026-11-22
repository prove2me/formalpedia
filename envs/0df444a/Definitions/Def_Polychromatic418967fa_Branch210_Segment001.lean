-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch210_Segment001
-- name    : Polychromatic418967fa_Branch210_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:35:56.090837+00:00
-- url     : https://prove2.me/theorems/d3c84cb1-08db-4e3d-a7bc-0a60043d05db
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch210_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_210_segment_001 : allB 165 210 :=
  allB_succ' 47 164 210 (Eq.refl Bool.true) (allA_succ_of_gcd 46 164 210 2 23 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 210 2 22 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 210 (accept_3_4 43 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 210 2 21 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 164 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 210 2 20 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 210 2 19 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 210 (accept_3_4 37 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 210 2 18 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 164 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 164 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 210 2 17 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 210 2 16 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 164 210 (accept_3_4 31 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 164 210 2 15 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 210 (Polychromatic418967fa.accept_17_12_11_6_1_3729 29 164 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 210 2 14 82 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 210 2 13 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 210 (accept_3_4 25 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 210 2 12 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 164 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 210 2 11 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 210 2 10 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 210 (accept_3_4 19 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 210 2 9 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 164 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 164 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 210 2 8 82 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 210 2 7 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 210 (accept_3_4 13 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 210 2 6 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 164 210 (Polychromatic418967fa.accept_19_11_12_1_1_11049 11 164 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 210 2 5 82 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 210
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 210 2 4 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 210 (accept_3_4 7 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  210 2 3 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 164 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 210 2 2 82 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 164 210 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 164 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 210 2 1 82 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 210 (accept_3_4 1 164 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164 210))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  48 163 210 (Eq.refl Bool.true) (allA_succ_of_accept 47 163 210 (accept_3_5 47 163 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 163 210 (Polychromatic418967fa.accept_17_12_10_6_1_3691 46 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 210 (accept_3_5 44 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 163 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 210 (accept_3_5 41 163 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 210
  (Polychromatic418967fa.accept_18_3_1_12_1_4419 39 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 210 (accept_3_5 38 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 210 (Polychromatic418967fa.accept_23_13_2_3_1_12451 36 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 210 (accept_3_5 35 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 163 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 210 (accept_3_5 32 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 210 (Polychromatic418967fa.accept_24_6_19_18_1_12450 30 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 210 (accept_3_5 29 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 210 (Polychromatic418967fa.accept_19_9_11_1_1_8239 28 163
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 210
  (Polychromatic418967fa.accept_19_8_11_1_1_8320 27 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 210 (accept_3_5 26 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 163 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 210 (accept_3_5 23 163 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 210 (accept_3_5 20 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 210 (Polychromatic418967fa.accept_20_19_3_10_1_3588 19 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 210 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 210 (accept_3_5 17 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 163 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 210 (accept_3_5 14 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 210 (Polychromatic418967fa.accept_17_12_10_6_1_3691 12 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 210 (accept_3_5 11 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 210 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 163
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 210 (accept_3_5 8 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 163 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 210 (accept_3_5 5 163 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 163 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 210
  (Polychromatic418967fa.accept_18_3_1_12_1_4419 3 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 210 (accept_3_5 2 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 210)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 162 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 162 210 6 8 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 210 (Polychromatic418967fa.accept_13_8_6_2_1_865 47 162 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 210 2 23 81 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 162 210 3 15 54 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 210 2 22 81 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 210
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 162 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 210 6 7 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 162 210 (Polychromatic418967fa.accept_19_3_10_1_1_12449 41 162 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 210 2 20 81 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 162 210 3 13 54 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 162 210 2 19 81 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 210
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 162 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 210 6 6 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 162 210 (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 162 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 210 2 17 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 162 210 3 11 54 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 210 2 16 81 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 210
  (Polychromatic418967fa.accept_25_6_12_10_1_12448 31 162 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 162 210 6 5 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 162 210 (Polychromatic418967fa.accept_22_7_8_12_1_12344 29 162 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 210 2 14 81 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 210 3 9 54 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 210 2 13 81 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 210
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 25 162 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 210 6 4 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 162 210 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 162 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 210 2 11 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 210 3 7 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 210 2 10 81 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 210
  (Polychromatic418967fa.accept_25_19_12_10_1_12447 19 162 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 162 210 6 3 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 162 210 (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 162 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 210 2 8 81 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 210 3 5 54 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 210 2 7 81 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 210
  (Polychromatic418967fa.accept_19_13_10_1_1_8236 13 162 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 210 6 2 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 210 (Polychromatic418967fa.accept_19_11_10_1_1_2773 11 162 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 210 2 5 81 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 210 3 3 54 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 210 2 4 81 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 210
  (Polychromatic418967fa.accept_19_7_10_1_1_5382 7 162 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 210 6 1 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 210 (Polychromatic418967fa.accept_20_5_2_10_1_3576 5 162 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 210 2 2 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 210 3 1 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 210 2 1 81 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 210 (Polychromatic418967fa.accept_13_1_6_2_1_377 1
  162 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  210))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 161 210 (Eq.refl Bool.true) (allA_succ_of_gcd 49
  161 210 7 7 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  48 161 210 (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 161 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 210 (accept_3_4 46 161 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 210 (Polychromatic418967fa.accept_18_9_17_12_1_462 45 161 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 210
  (Polychromatic418967fa.accept_16_12_1_2_1_2163 44 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 210 (accept_3_4 43 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  161 210 7 6 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 161 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 161 210 (accept_3_4 40 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 161 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 161 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 161 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 210 (accept_3_4 37 161 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 210
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 161 210 7 5 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 161 210 (accept_3_4 34 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 161 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 210 (accept_3_4 31 161 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 210 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 161 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 161 210 7 4 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 161 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 210 (Polychromatic418967fa.accept_17_9_8_6_1_6050 26 161
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 210 (accept_3_4 25 161
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 24 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 161 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 210 (accept_3_4 22 161 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 161 210 7 3 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 161 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 161 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 210 (accept_3_4 19 161 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 210 (Polychromatic418967fa.accept_22_18_7_12_1_9213 18 161
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 210
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 210 (accept_3_4 16 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 161 210 7 2 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 161 210 (accept_3_4 13 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 161 210 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 161 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 210 (accept_3_4 10 161 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 210 (Polychromatic418967fa.accept_13_9_5_2_1_2185
  9 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 210
  (Polychromatic418967fa.accept_19_8_9_1_1_3990 8 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 161 210 7 1 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 161 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 161 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 161 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 210 (accept_3_4 4 161 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 210 (accept_3_4 1 161 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  210)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 160 210 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  160 210 10 5 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 160 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 160 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 160 210 2 24 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 160 210 (accept_3_5 47 160 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 160 210 2 23 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 160 210 5 9 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 160 210 2 22 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 210
  (Polychromatic418967fa.accept_23_20_22_3_1_12393 43 160 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 160 210 2 21 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 160 210 (accept_3_5 41 160 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 210 10 4 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 160 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 160 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 210 2 19 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 160 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 210 2 18 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 160 210 5 7 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 160 210 2 17 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 160 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 160 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 210 2 16 80 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 160 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 210 10 3 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 160 210 (accept_3_5 29 160 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 210 2 14 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 160 210 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 160 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 210 2 13 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 160 210 5 5 32 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 160 210 2 12 80 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 210 (accept_3_5 23 160 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 210 2 11 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 210
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 160 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 160 210 10 2 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 160 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 160 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 210 2 9 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 210 (accept_3_5 17 160 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 210 2 8 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 160 210 5 3 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 160 210 2 7 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 160 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 210 2 6 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 160 210 (accept_3_5 11 160 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 210 10 1 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 160 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 160 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 210 2 4 80 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 210
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 160 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 160 210 2 3 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 160 210 5 1 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 160 210 2 2 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 160 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 160 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 210 2 1 80 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 1
  160 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  210))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 159 210 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  159 210 3 17 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 159 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 159 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 159 210 3 16 53 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 159 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 159 210 3 15 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 159 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 159 210 3 14 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 159 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 159 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 210 (Polychromatic418967fa.accept_9_4_6_3_1_179
  40 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 159 210 3 13 53 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 159 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 159 210 3 12 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 159 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 159 210 3 11 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 159 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 159 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 210 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 210 3 10 53 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 210 3 9 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 26
  159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 159 210 3 8 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 159 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 159 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 210 3 7 53 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 210 3 6 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 159 210 3 5 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 159 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 210 3 4 53 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 210 3 3 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 159 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 159 210 3 2 53 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 159 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 159 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 210 3 1 53 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 159 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159 210)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  158 210 (Eq.refl Bool.true) (allA_succ_of_gcd 52 158 210 2 26 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 158 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 158 210 2 25 79 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 158 210 (accept_3_4 49
  158 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 158 210 2 24 79 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 158 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 158 210 2 23 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 158 210 (Polychromatic418967fa.accept_12_9_2_6_1_455 45 158 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 158 210 2 22 79 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 158 210 (accept_3_4 43 158 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 158 210 2 21 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 158 210 (Polychromatic418967fa.accept_11_8_4_1_1_1000
  41 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 210 2 20 79 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 210 2 19 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 210 (accept_3_4 37 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 210 2 18 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 158 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 210 2 17 79 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 210 2 16 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 210 (accept_3_4 31 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 210 2 15 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 158 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 210 2 14 79 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 210 2 13 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 210 (accept_3_4 25 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 210 2 12 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 210 (Polychromatic418967fa.accept_22_1_4_12_1_12446 23 158 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 210 2 11 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 210 2 10 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 210 (accept_3_4 19 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 210 2 9 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 158 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 210 2 8 79 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 210 2 7 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 210 (accept_3_4 13 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 210 2 6 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 158 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 210 2 5 79 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 210 2 4 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 210 (accept_3_4 7 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  210 2 3 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 210 (Polychromatic418967fa.accept_19_5_6_1_1_5366 5 158 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 210 2 2 79 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 158 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 210 2 1 79 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 210 (accept_3_4 1 158 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 210)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 157 210 (Eq.refl Bool.true) (allA_succ_of_accept 53 157 210 (accept_3_5 53 157 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 210 (accept_3_5 50 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 210 (Polychromatic418967fa.accept_20_9_17_10_1_3633 49 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 210 (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 210 (accept_3_5 47 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 157 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 210
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 45 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 210 (accept_3_5 44 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 157 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 210 (accept_3_5 41 157 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 210 (Polychromatic418967fa.accept_26_14_1_2_1_10584 40 157 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 210 (accept_3_5 38 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 210 (Polychromatic418967fa.accept_17_2_4_6_1_1619 36 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 210 (accept_3_5 35 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 157 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 210 (accept_3_5 32 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 210 (Polychromatic418967fa.accept_23_7_19_3_1_12427 30 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 210 (accept_3_5 29 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 157 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 210 (accept_3_5 26 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 157 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 210 (accept_3_5 23 157 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 210 (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 210
  (Polychromatic418967fa.accept_16_5_13_2_1_2138 21 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 210 (accept_3_5 20 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 210 (Polychromatic418967fa.accept_19_18_5_1_1_8255 18 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 210 (accept_3_5 17 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 157 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 210 (accept_3_5 14 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 210 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 210 (accept_3_5 11 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 157 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 210
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 210 (accept_3_5 8 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 157 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 210 (accept_3_5 5 157 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 210 (Polychromatic418967fa.accept_19_4_5_1_1_4077 4 157 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 210 (accept_3_5 2 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 157 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 210)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 156 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 156 210 6 9 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 210 (Polychromatic418967fa.accept_19_15_4_1_1_4060 53 156 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 210 2 26 78 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 156 210 3 17 52 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 156 210 2 25 78 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 210
  (Polychromatic418967fa.accept_16_1_12_2_1_2136 49 156 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 210 6 8 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 156 210 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 156 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 210 2 23 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 156 210 3 15 52 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 156 210 2 22 78 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 210
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 156 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 210 6 7 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 156 210 (Polychromatic418967fa.accept_16_9_12_2_1_3093 41 156 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 210 2 20 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 156 210 3 13 52 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 210 2 19 78 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 210
  (Polychromatic418967fa.accept_24_13_12_18_1_8910 37 156 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 156 210 6 6 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 156 210 (Polychromatic418967fa.accept_17_1_3_6_1_3672 35 156 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 210 2 17 78 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 156 210 3 11 52 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 210 2 16 78 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 210
  (Polychromatic418967fa.accept_16_15_12_2_1_6502 31 156 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 156 210 6 5 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 156 210 (Polychromatic418967fa.accept_19_10_4_1_1_4018 29 156 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 210 2 14 78 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 156 210 3 9 52 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 210 2 13 78 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 210
  (Polychromatic418967fa.accept_11_3_2_1_1_994 25 156 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 210 6 4 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 156 210 (Polychromatic418967fa.accept_16_7_12_2_1_8902 23 156 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 210 2 11 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 156 210 3 7 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 156 210 2 10 78 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 210
  (Polychromatic418967fa.accept_20_19_16_10_1_12445 19 156 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 156 210 6 3 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 156 210 (Polychromatic418967fa.accept_16_1_12_2_1_2136 17 156 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 210 2 8 78 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 156 210 3 5 52 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 156 210 2 7 78 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 210
  (Polychromatic418967fa.accept_24_13_12_18_1_8910 13 156 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 156 210 6 2 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 156 210 (Polychromatic418967fa.accept_24_11_12_18_1_12444 11 156 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 210 2 5 78 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 156 210 3 3 52 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 156 210 2 4 78 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 210
  (Polychromatic418967fa.accept_16_7_12_2_1_8902 7 156 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 210 6 1 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 210 (Polychromatic418967fa.accept_17_5_3_6_1_12347 5 156 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 210 2 2 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 210 3 1 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 210 2 1 78 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 210 (Polychromatic418967fa.accept_16_1_12_2_1_2136
  1 156 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 155 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 155 210 5 11 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 155 210 (Polychromatic418967fa.accept_16_6_11_2_1_6485 54 155 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 210 (accept_3_4 52 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 155 210 5 10 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 155 210 (accept_3_4 49 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 155 210 (Polychromatic418967fa.accept_19_10_3_1_1_8312 48 155 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 210 (Polychromatic418967fa.accept_17_13_2_6_1_3683 47 155
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 210 (accept_3_4 46 155
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 155 210 5 9 31 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 155 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 210 (accept_3_4 43 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 155 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 155 210 5 8 31 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 155 210
  (Polychromatic418967fa.accept_16_7_11_2_1_3117 39 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 155 210 (Polychromatic418967fa.accept_16_6_11_2_1_6485 38 155 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 210 (accept_3_4 37 155 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 155 210 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 155 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 155 210 5 7 31 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 155 210 (accept_3_4 34 155 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 210 (accept_3_4 31 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  155 210 5 6 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 155 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 155 210 (accept_3_4 28 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 155 210 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 155 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 155 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 155 210 5 5 31 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 155 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 24 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 155 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 155 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 210 (accept_3_4 22 155 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 155 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 155 210 5 4 31 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 155 210 (accept_3_4 19 155 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 210 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 155
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 210 (accept_3_4 16 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  155 210 5 3 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 155 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 155 210 (accept_3_4 13 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 155 210 (Polychromatic418967fa.accept_17_12_2_6_1_2630 12 155 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 210 (Polychromatic418967fa.accept_19_11_3_1_1_2799 11 155
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 155 210 5 2 31 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 155 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 155 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 155 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 210 (accept_3_4 7 155 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 155 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 155 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 155 210 5 1 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 155 210 (accept_3_4 4 155 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 210 (Polychromatic418967fa.accept_13_3_12_2_1_385 3 155 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 210
  (Polychromatic418967fa.accept_19_2_3_1_1_8309 2 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 210 (accept_3_4 1 155 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 154 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 154 210 14 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 154 210 (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 154 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 154 210 2 27 77 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 154 210 (accept_3_5 53 154 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 154 210 2 26 77 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 154 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 154 210 2 25 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 154 210 7 7 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 154 210 2 24 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 154 210 (accept_3_5 47 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 154 210 2 23 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 154 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 154 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 210 2 22 77 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 210 14 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 210 (accept_3_5 41 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 210 2 20 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 154 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 210 2 19 77 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 210
  (Polychromatic418967fa.accept_17_3_1_6_1_251 37 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 210 2 18 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 154 210 7 5 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 154 210 2 17 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 154 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 154 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 210 2 16 77 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 210 2 15 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 210 (accept_3_5 29 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 210 14 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 154 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 210 2 13 77 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 210 2 12 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 210 (accept_3_5 23 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 210 2 11 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 154 210 7 3 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 154 210 2 10 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 154 210 (Polychromatic418967fa.accept_17_2_1_6_1_3777 19 154 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 154 210 2 9 77 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 154 210 (accept_3_5 17 154 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 154 210 2 8 77 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 154 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 154 210 14 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 154 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 154 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 210 2 6 77 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 210 (accept_3_5 11 154 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 210 2 5 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 9
  154 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 210 2 4 77 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 154 210 7 1 22 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 154 210 2 3 77 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 210 (accept_3_5 5
  154 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154 210 2 2 77 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 154 210
  (Polychromatic418967fa.accept_12_3_10_6_1_442 3 154 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 154 210 2 1 77 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 154 210 (Polychromatic418967fa.accept_20_1_14_10_1_12443 1 154 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 154 210))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  58 153 210 (Eq.refl Bool.true) (allA_succ_of_gcd 57 153 210 3 19 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 153 210 (Polychromatic418967fa.accept_12_8_9_6_1_127
  56 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 153 210 3 18 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 153 210 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 153 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 52 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 153 210 3 17 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 153 210 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 153 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 210 (Polychromatic418967fa.accept_16_1_9_2_1_4161
  49 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 153 210 3 16 51 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 153 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 210 (Polychromatic418967fa.accept_11_2_10_1_1_1017 46 153 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 153 210 3 15 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 153 210 (Polychromatic418967fa.accept_12_8_9_6_1_127
  44 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 153 210 3 14 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 153 210 (Polychromatic418967fa.accept_18_5_9_12_1_8461 41 153 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 40 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 210 3 13 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 210 (Polychromatic418967fa.accept_12_2_9_6_1_439 38 153 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 210
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 37 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 153 210 3 12 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 153 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 153 210 3 11 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 153 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 153 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 210 3 10 51 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 210
  (Polychromatic418967fa.accept_13_3_10_2_1_381 29 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 153 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 210 3 9 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 210 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 210
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 153 210 3 8 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 153 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 153 210 3 7 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 153 210 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 153 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 210 3 6 51 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 210
  (Polychromatic418967fa.accept_16_1_9_2_1_4161 17 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 153 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 210 3 5 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 210 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 210
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 153 210 3 4 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 153 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 210 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 153
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 210 3 3 51 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 210
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 210 3 2 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 210 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 153 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 153 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 210 3 1 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 210 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 153 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 210 (Polychromatic418967fa.accept_16_1_9_2_1_4161 1 153 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 152 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 152 210 2 29 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 152 210 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 152 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 152 210 2 28 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 152 210 (accept_3_4 55 152 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 152 210 2 27 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 152 210 (Polychromatic418967fa.accept_13_1_9_2_1_1448
  53 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 210 2 26 76 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 210 2 25 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 210 (accept_3_4 49 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 210 2 24 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 152 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 210 2 23 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 210 2 22 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 210 (accept_3_4 43 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 210 2 21 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 152 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 210 2 20 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 210 2 19 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 210 (accept_3_4 37 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 210 2 18 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 210 (Polychromatic418967fa.accept_20_15_12_10_1_1291 35 152 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 210 2 17 76 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 210 2 16 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 210 (accept_3_4 31 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 210 2 15 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 152 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 210 2 14 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 210 2 13 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 210 (accept_3_4 25 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 210 2 12 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 152 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 210 2 11 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 210
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 210 2 10 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 210 (accept_3_4 19 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 210 2 9 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 210 (Polychromatic418967fa.accept_22_17_20_12_1_10795 17 152 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 210 2 8 76 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 210 2 7 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 210 (accept_3_4 13 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 210 2 6 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 152 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 152 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 210 2 5 76 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 210 2 4 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 210 (accept_3_4 7 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  210 2 3 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 152 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 210 2 2 76 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 152 210 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 152 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 210 2 1 76 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 210 (accept_3_4 1 152 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 151 210 (Eq.refl Bool.true) (allA_succ_of_accept 59 151 210 (accept_3_5 59 151 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 210 (accept_3_5 56 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 210 (Polychromatic418967fa.accept_20_14_11_10_1_11036 54 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 210 (accept_3_5 53 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 210 (Polychromatic418967fa.accept_19_14_18_1_1_12442 52
  151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 210
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 210 (accept_3_5 50 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 210 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 210 (accept_3_5 47 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 151 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 210 (accept_3_5 44 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 210 (Polychromatic418967fa.accept_16_11_7_2_1_4185 43 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 151 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 210 (accept_3_5 41 151 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 210
  (Polychromatic418967fa.accept_18_3_7_12_1_1196 39 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 210 (accept_3_5 38 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 210 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 210 (accept_3_5 35 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 210 (Polychromatic418967fa.accept_20_14_11_10_1_11036 34
  151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 210 (accept_3_5 32 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 210 (Polychromatic418967fa.accept_19_11_18_1_1_4048 30 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 210 (accept_3_5 29 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 151 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 210
  (Polychromatic418967fa.accept_16_11_7_2_1_4185 27 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 210 (accept_3_5 26 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 151 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 210 (accept_3_5 23 151 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 210 (accept_3_5 20 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 210 (Polychromatic418967fa.accept_27_18_16_21_1_12441 18 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 210 (accept_3_5 17 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 210 (Polychromatic418967fa.accept_22_16_19_12_1_4348 16
  151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 210
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 210 (accept_3_5 14 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 210 (Polychromatic418967fa.accept_16_12_7_2_1_4159 12 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 210 (accept_3_5 11 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 151 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 210 (accept_3_5 8 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 210 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 151 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 210 (accept_3_5 5 151 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 151 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 210
  (Polychromatic418967fa.accept_18_3_7_12_1_1196 3 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 210 (accept_3_5 2 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 150 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 150 210 30 2 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 150 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 150 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 210 2 29 75 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 150 210 3 19 50 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 150 210 2 28 75 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 150 210 5 11 30
  42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 150 210 6 9 25
  35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 150 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 210 2 26 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 150 210 3 17 50 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 150 210 10 5 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 150 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 150 210 6 8 25 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 150 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 150 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 210 2 23 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 150 210 15 3 10 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 210 2 22 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 150 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 210 6 7 25 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 210
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 150 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 210 10 4 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 150 210 3 13 50 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 210 2 19 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 150 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 210 6 6 25 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 150 210 5 7 30 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 150 210 2 17 75 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 150 210 3 11 50
  70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 210 2 16
  75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 150 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 210 30 1 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 150 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 150 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 210 2 14 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 150 210 3 9 50 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 150 210 2 13 75 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 150 210 5 5 30 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 150 210 6 4 25 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 210
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 150 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 210 2 11 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 150 210 3 7 50 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 150 210 10 2 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 150 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 150 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 210 6 3 25 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 150 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 210 2 8 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 150 210 15 1 10 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 210 2 7 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 150 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 210 6 2 25 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 150 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 210 10 1 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 150 210 3 3 50 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 150 210 2 4 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 150 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 150 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 210 6 1 25 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 150 210 5 1 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 150 210 2 2 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 210 3 1 50 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 210 2 1 75 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 1
  150 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 149 210 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 149 210 (accept_3_4 61 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 210 (accept_3_4 58 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 210 (Polychromatic418967fa.accept_20_17_9_10_1_12382 57 149 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 210 (accept_3_4 55 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 210 (Polychromatic418967fa.accept_23_8_11_3_1_12440 54 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 210 (accept_3_4 52 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 149 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 210
  (Polychromatic418967fa.accept_22_6_17_12_1_7704 50 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 149 210 (accept_3_4 49 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 149 210 (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 149 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 149 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 210 (accept_3_4 46 149 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 210
  (Polychromatic418967fa.accept_16_13_5_2_1_2131 45 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 149 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 44 149 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 210 (accept_3_4 43 149 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 149 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 210 (Polychromatic418967fa.accept_17_7_13_6_1_811
  41 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 210 (accept_3_4 40
  149 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 149 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 149 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 210 (accept_3_4 37 149 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 149 210 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 149 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 210 (accept_3_4 34 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 210 (Polychromatic418967fa.accept_19_13_16_1_1_4044 32 149 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 210 (accept_3_4 31 149 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 210 (Polychromatic418967fa.accept_13_4_6_2_1_1437 30 149
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 210 (accept_3_4 28 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 210 (accept_3_4 25 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 149 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 210 (accept_3_4 22 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 210 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 210 (accept_3_4 19 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 210 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 149 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 210 (accept_3_4 16 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 210 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 149 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 210 (accept_3_4 13 149 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 210 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 149
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 210 (accept_3_4 10 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 210 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 210 (accept_3_4 7 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 149 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 210
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 210 (accept_3_4 4 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 210 (accept_3_4 1 149 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  148 210 (Eq.refl Bool.true) (allA_succ_of_gcd 62 148 210 2 31 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 148 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 148 210 2 30 74 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 148 210 (accept_3_5 59
  148 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 148 210 2 29 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 148 210
  (Polychromatic418967fa.accept_12_9_4_6_1_460 57 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 148 210 2 28 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 148 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 148 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 148 210 2 27 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 148 210 (accept_3_5 53 148 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 148 210 2 26 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 148 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 51
  148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 210 2 25 74 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 210
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 210 2 24 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 210 (accept_3_5 47 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 210 2 23 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 148 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 210 2 22 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 210 2 21 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 210 (accept_3_5 41 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 210 2 20 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 210 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 148 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 210 2 19 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 210 2 18 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 148 210 (accept_3_5 35 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 210 2 17 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 148 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 210 2 16 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 210
  (Polychromatic418967fa.accept_27_4_13_21_1_8510 31 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 148 210 2 15 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 148 210 (accept_3_5 29 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 210 2 14 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 148 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 148 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 210 2 13 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 210 2 12 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 148 210 (accept_3_5 23 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 210 2 11 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 148 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 210 2 10 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 210 2 9 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 210 (accept_3_5 17 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 210 2 8 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 148 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 148 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 210 2 7 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 210
  (Polychromatic418967fa.accept_23_13_10_3_1_12439 13 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 148 210 2 6 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 148 210 (accept_3_5 11 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 210 2 5 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 148 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 210 2 4 74 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 148 210 2 3 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 210 (accept_3_5 5 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  210 2 2 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 148 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 210 2 1 74 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 148 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 148 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 147 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 147 210 21 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 147 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 147 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 147 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 147 210 3 20 49 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 147 210
  (Polychromatic418967fa.accept_19_2_14_1_1_11076 59 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 147 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 147 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 147 210 3 19 49 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 147 210 7 8 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 147 210
  (Polychromatic418967fa.accept_17_4_11_6_1_3730 55 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 147 210 3 18 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 147 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 210 (Polychromatic418967fa.accept_11_8_4_1_1_1000
  52 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 147 210 3 17 49 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 147 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 147 210 7 7 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 147 210 3 16 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 147 210 (Polychromatic418967fa.accept_16_15_3_2_1_4170 47 147 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 210
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 147 210 3 15 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 147 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 147 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 210
  (Polychromatic418967fa.accept_18_7_3_12_1_3241 43 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 147 210 21 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 147 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 210 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 147
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 210 3 13 49 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 147 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 147 210 3 12 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 147 210 7 5 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 147 210 (Polychromatic418967fa.accept_12_10_3_6_1_882
  34 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 147 210 3 11 49 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 147 210
  (Polychromatic418967fa.accept_12_8_3_6_1_909 32 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 210 (Polychromatic418967fa.accept_13_5_4_2_1_846 31 147 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 210 3 10 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 147 210 7 4 21 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 147 210 3 9 49 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 210 3 8 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 210
  (Polychromatic418967fa.accept_20_3_7_10_1_11035 23 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 147 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 147 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 210 21 1 7 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 210
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 210 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 147 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 210 3 6 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 210
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 147 210 3 5 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 147 210 7 2 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 210 3 4 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 210 (Polychromatic418967fa.accept_13_11_4_2_1_2954
  11 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 210
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 147 210 3 3 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 210 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 147 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147 210 7 1 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 147 210 3 2 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 210
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 147 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 210 3 1 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 147 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 146 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 146 210 2 32 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 146 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 63 146 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 146 210 2 31 73 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 146 210 (accept_3_4 61 146 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 146 210 2 30 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 146 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 59
  146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 210 2 29 73 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 210
  (Polychromatic418967fa.accept_11_2_3_1_1_244 57 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 210 2 28 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 210 (accept_3_4 55 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 210 2 27 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 146 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 210 2 26 73 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 210 2 25 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 210 (accept_3_4 49 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 210 2 24 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 210 (Polychromatic418967fa.accept_22_3_14_12_1_7651 47 146 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 210 2 23 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 210 2 22 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 210 (accept_3_4 43 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 210 2 21 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 146 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 210 2 20 73 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 210 2 19 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 210 (accept_3_4 37 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 210 2 18 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 146 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 210 2 17 73 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 210 2 16 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 210 (accept_3_4 31 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 210 2 15 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 210 (Polychromatic418967fa.accept_17_12_10_6_1_3691 29 146 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 210 2 14 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 210 2 13 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 210 (accept_3_4 25 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 210 2 12 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 146 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 210 2 11 73 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 210 2 10 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 210 (accept_3_4 19 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 210 2 9 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 146 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 210 2 8 73 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 210 2 7 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 210 (accept_3_4 13 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 210 2 6 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 210 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 146 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 210 2 5 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 210 2 4 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 210 (accept_3_4 7 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  210 2 3 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 146 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 210 2 2 73 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 146 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 210 2 1 73 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 210 (accept_3_4 1 146 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 145 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 145 210 5 13 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 145 210 (Polychromatic418967fa.accept_19_7_12_1_1_6830 64 145 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 210 (accept_3_5 62 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 145 210 5 12 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 145 210 (accept_3_5 59 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 145 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 145 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 210 (Polychromatic418967fa.accept_16_9_1_2_1_2126 57 145
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 210 (accept_3_5 56 145
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 145 210 5 11 29 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 145 210
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 145 210 (accept_3_5 53 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 145 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 145 210 5 10 29 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 145 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 145 210 (Polychromatic418967fa.accept_20_8_5_10_1_11023 48 145 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 210 (accept_3_5 47 145 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 210 (Polychromatic418967fa.accept_19_8_12_1_1_11084 46 145 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 145 210 5 9 29 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 145 210 (accept_3_5 44
  145 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 145 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 145 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 210 (accept_3_5 41 145 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 145 210 5 8 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 145 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 145 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 210 (accept_3_5 38 145 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 210 (Polychromatic418967fa.accept_17_3_9_6_1_3726 37 145
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 210
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 145 210 5 7 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 145 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 145 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 145 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 210 (accept_3_5 32 145 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 210 5 6 29 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 210 (accept_3_5 29
  145 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 210
  (Polychromatic418967fa.accept_16_12_1_2_1_2163 28 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 145 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 145 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 210 (accept_3_5 26 145 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 145 210 5 5 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 145 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 145 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 210 (accept_3_5 23 145 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 145 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 210
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 145 210 5 4 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 145 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 210 (Polychromatic418967fa.accept_19_18_12_1_1_9737 18 145
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 210 (accept_3_5 17 145
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 16 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 145 210 5 3 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 145 210 (accept_3_5 14 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 210 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 145 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 210 (accept_3_5 11 145 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 145 210 5 2 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 145 210 (Polychromatic418967fa.accept_16_9_1_2_1_2126 9
  145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 210 (accept_3_5 8 145
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 210 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 145 210 5 1 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 145 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 145 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 210 (accept_3_5 2 145 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 210 (Polychromatic418967fa.accept_20_1_5_10_1_3534
  1 145 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 144 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 144 210 6 11 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 210 (Polychromatic418967fa.accept_17_14_8_6_1_2643 65 144 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 210 2 32 72 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 144 210 3 21 48 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 144 210 2 31 72 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 210
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 61 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 210 6 10 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 210 (Polychromatic418967fa.accept_25_9_19_10_1_12438 59 144 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 210 2 29 72 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 144 210 3 19 48 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 144 210 2 28 72 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 210
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 55 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 210 6 9 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 144 210 (Polychromatic418967fa.accept_19_15_11_1_1_12437 53 144 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 210 2 26 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 144 210 3 17 48 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 144 210 2 25 72 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 210
  (Polychromatic418967fa.accept_17_15_8_6_1_8733 49 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 210 6 8 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 144 210 (Polychromatic418967fa.accept_19_9_11_1_1_8239 47 144 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 210 2 23 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 144 210 3 15 48 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 210 2 22 72 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 210
  (Polychromatic418967fa.accept_17_9_8_6_1_6050 43 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 210 6 7 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 144 210 (Polychromatic418967fa.accept_19_3_11_1_1_8319 41 144 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 210 2 20 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 144 210 3 13 48 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 210 2 19 72 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 210
  (Polychromatic418967fa.accept_19_18_11_1_1_4035 37 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 144 210 6 6 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 144 210 (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 144 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 210 2 17 72 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 144 210 3 11 48 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 210 2 16 72 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 210
  (Polychromatic418967fa.accept_17_14_8_6_1_2643 31 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 210 6 5 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 144 210 (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 144 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 210 2 14 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 144 210 3 9 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 144 210 2 13 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 210
  (Polychromatic418967fa.accept_13_12_1_2_1_845 25 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 210 6 4 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 210 (Polychromatic418967fa.accept_25_23_19_10_1_12420 23 144 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 210 2 11 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 210 3 7 48 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 210 2 10 72 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 210
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 210 6 3 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 210 (Polychromatic418967fa.accept_26_17_14_2_1_12436 17 144 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 210 2 8 72 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 144 210 3 5 48 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 210 2 7 72 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 210
  (Polychromatic418967fa.accept_25_13_19_10_1_3337 13 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 144 210 6 2 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 144 210 (Polychromatic418967fa.accept_20_11_4_10_1_12378 11 144 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 210 2 5 72 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 144 210 3 3 48 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 144 210 2 4 72 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 210
  (Polychromatic418967fa.accept_27_7_9_21_1_12435 7 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 210 6 1 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 210 (Polychromatic418967fa.accept_20_5_4_10_1_3529 5 144 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 210 2 2 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 210 3 1 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 210 2 1 72 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 210 (Polychromatic418967fa.accept_20_1_4_10_1_3645
  1 144 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 143 210 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 143 210 (accept_3_4 67 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 143 210 (Polychromatic418967fa.accept_19_9_10_1_1_8329 66 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 143 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 210 (accept_3_4 64 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 210 (Polychromatic418967fa.accept_18_9_17_12_1_462 63 143 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 210
  (Polychromatic418967fa.accept_20_2_3_10_1_5075 62 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 143 210 (accept_3_4 61 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 143 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 143 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 210 (accept_3_4 58 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 143 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 210 (accept_3_4 55 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 210 (Polychromatic418967fa.accept_19_16_10_1_1_11073 54 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 143 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 210 (accept_3_4 52 143 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 143 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 210
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 210 (accept_3_4 49 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 210 (Polychromatic418967fa.accept_17_14_7_6_1_11222 48 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 210 (accept_3_4 46 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 143 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 210
  (Polychromatic418967fa.accept_16_12_15_2_1_6473 44 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 143 210 (accept_3_4 43 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 143 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 143 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 210 (accept_3_4 40 143 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 210
  (Polychromatic418967fa.accept_20_19_3_10_1_3588 39 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 210 (accept_3_4 37 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 210 (Polychromatic418967fa.accept_19_17_10_1_1_6795 36 143 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 210
  (Polychromatic418967fa.accept_16_3_15_2_1_6475 35 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 210 (accept_3_4 34 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 210 (accept_3_4 31 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 210 (Polychromatic418967fa.accept_17_13_7_6_1_827 30 143 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 210 (accept_3_4 28 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 210 (Polychromatic418967fa.accept_18_9_17_12_1_462 27 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 210 (Polychromatic418967fa.accept_19_7_10_1_1_5382 26 143 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 210 (accept_3_4 25 143 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 143 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 210
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 210 (accept_3_4 22 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 210 (accept_3_4 19 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 210 (Polychromatic418967fa.accept_22_18_11_12_1_12434 18 143 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 210 (accept_3_4 16 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 210 (accept_3_4 13 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 210 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 143 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 210 (accept_3_4 10 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 210 (Polychromatic418967fa.accept_22_8_11_12_1_12433 8 143 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 210 (accept_3_4 7 143 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 143 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 210 (accept_3_4 4 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 210 (Polychromatic418967fa.accept_16_3_15_2_1_6475 3 143 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 210 (accept_3_4 1 143 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  69 142 210 (Eq.refl Bool.true) (allA_succ_of_gcd 68 142 210 2 34 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 67
  142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 142 210 2 33 71 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 142 210 (accept_3_5 65
  142 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 142 210 2 32 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 142 210
  (Polychromatic418967fa.accept_12_3_10_6_1_442 63 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 142 210 2 31 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 142 210 (Polychromatic418967fa.accept_23_15_4_3_1_12418 61 142 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 142 210 2 30 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 142 210 (accept_3_5 59 142 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 142 210 2 29 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 142 210
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 142 210 2 28 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 142 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 142 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 142 210 2 27 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 142 210 (accept_3_5 53 142 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 142 210 2 26 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 142 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 51
  142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 210 2 25 71 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 210 2 24 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 210 (accept_3_5 47 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 210 2 23 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 142 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 210 2 22 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 210
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 210 2 21 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 210 (accept_3_5 41 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 210 2 20 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 142 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 210 2 19 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 210 2 18 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 210 (accept_3_5 35 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 210 2 17 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 142 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 210 2 16 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 210 2 15 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 210 (accept_3_5 29 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 210 2 14 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 142 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 210 2 13 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 210
  (Polychromatic418967fa.accept_20_5_2_10_1_3576 25 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 210 2 12 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 210 (accept_3_5 23 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 210 2 11 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 142 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 210 2 10 71 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 210 2 9 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 210 (accept_3_5 17 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 210 2 8 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 142 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 210 2 7 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 210 2 6 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 210 (accept_3_5 11 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 210 2 5 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 210 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 142 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 210 2 4 71 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 210
  (Polychromatic418967fa.accept_22_7_10_12_1_12348 7 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 142 210 2 3 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 142 210 (accept_3_5 5 142 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 142 210 2 2 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 142 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 142 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 210 2 1 71 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 1
  142 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 141 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 141 210 3 23 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 141 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 141 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 141 210 3 22 47 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 141 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 141 210 3 21 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 141 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 141 210 3 20 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 141 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 141 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 210 (Polychromatic418967fa.accept_9_4_6_3_1_179
  58 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 141 210 3 19 47 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 141 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 141 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 141 210 3 18 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 141 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 53
  141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 141 210 3 17 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 141 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 141 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 210 (Polychromatic418967fa.accept_9_4_6_3_1_179
  49 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 141 210 3 16 47 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 141 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 141 210 3 15 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 141 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 141 210 3 14 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 141 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 141 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 210 (Polychromatic418967fa.accept_9_4_6_3_1_179
  40 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 141 210 3 13 47 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 141 210 3 12 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 141 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 141 210 3 11 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 141 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 141 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 210 3 10 47 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 141 210 3 9 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 141 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 26
  141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 141 210 3 8 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 141 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 141 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 210 3 7 47 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 210 3 6 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 141 210 3 5 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 141 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 141 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 210 3 4 47 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 210 3 3 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 141 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 210 3 2 47 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 141 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 210 3 1 47 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 141 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 141 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 140 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 140 210 70 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 140 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 140 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 140 210 2 34 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 140 210 (accept_3_4 67 140 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 140 210 2 33 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 140 210 5 13 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 140 210 2 32 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 140 210 7 9 20 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 140 210 2 31 70 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 140 210 (accept_3_4 61 140 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 140 210 10 6 14 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 140 210
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 140 210 2 29 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 140 210 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 140 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 140 210 14 4 10 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 140 210 5 11 28 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 140 210 2 27 70 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 140 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 140 210 2 26 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 140 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 140 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 140 210 10 5 14 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 140 210 7 7 20 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 140 210 2 24 70 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 140 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 140 210 2 23 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 140 210 5 9 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 140 210 2 22 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 140 210 (accept_3_4 43 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 210 14 3 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 210 (Polychromatic418967fa.accept_16_9_12_2_1_3093 41 140 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 210 10 4 14 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 210 2 19 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 210 (accept_3_4 37 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 210 2 18 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 140 210 35 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 140 210 2 17 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 140 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 140 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 210 2 16 70 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 210 (accept_3_4 31 140 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 210 10 3 14 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 140 210 14 2 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 140 210 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 140 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 140 210 2 13 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 140 210 5 5 28 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 140 210 2 12 70 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 210
  (Polychromatic418967fa.accept_16_7_12_2_1_8902 23 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 140 210 2 11 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 140 210 7 3 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 140 210 10 2 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 140 210 (accept_3_4 19 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 210 2 9 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 140 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 140 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 210 2 8 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 140 210 5 3 28 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 140 210 14 1 10 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 210 (accept_3_4 13 140 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 210 2 6 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 140 210 10 1 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 140 210 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 140 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 210 2 4 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 140 210 7 1 20 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 140 210 2 3 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 140 210 5 1 28 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 140 210 2 2 70 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 140 210 2 1 70 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 140 210 (accept_3_4 1 140 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 139 210 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 139 210 (accept_3_5 71 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 139 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 139 210 (accept_3_5 68 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 139 210 (Polychromatic418967fa.accept_19_10_6_1_1_6828 67 139 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 210
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 66 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 139 210 (accept_3_5 65 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 139 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 139 210 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 210 (accept_3_5 62 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 139 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 210 (accept_3_5 59 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 210 (Polychromatic418967fa.accept_13_6_9_2_1_838 58 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 210 (accept_3_5 56 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 210
  (Polychromatic418967fa.accept_16_6_11_2_1_6485 54 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 210 (accept_3_5 53 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 210 (accept_3_5 50 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 210
  (Polychromatic418967fa.accept_17_14_3_6_1_3716 48 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 210 (accept_3_5 47 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 210 (accept_3_5 44 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 139 210 (accept_3_5 41 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 139 210 (Polychromatic418967fa.accept_13_1_9_2_1_1448 40 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 139 210 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 210 (accept_3_5 38 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 139 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 210
  (Polychromatic418967fa.accept_20_16_19_10_1_12352 36 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 139 210 (accept_3_5 35 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 139 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 139 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 139 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 210 (accept_3_5 32 139 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 210 (Polychromatic418967fa.accept_13_5_9_2_1_1489
  31 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 210
  (Polychromatic418967fa.accept_19_11_6_1_1_2826 30 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 210 (accept_3_5 29 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 210 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 210 (accept_3_5 26 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 210 (accept_3_5 23 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 210 (Polychromatic418967fa.accept_16_6_11_2_1_6485 22 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 210 (accept_3_5 20 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 210
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 210 (accept_3_5 17 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 210 (accept_3_5 14 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 210
  (Polychromatic418967fa.accept_23_12_1_3_1_12432 12 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 139 210 (accept_3_5 11 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 139 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 139 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 210 (accept_3_5 8 139 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 7
  139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 210 (accept_3_5 5 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 210 (Polychromatic418967fa.accept_23_4_1_3_1_12431 4 139 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 210 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 210 (accept_3_5 2 139 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 138 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 138 210 6 12 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 210 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 138 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 210 2 35 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 138 210 3 23 46 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 138 210 2 34 69 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 210
  (Polychromatic418967fa.accept_20_7_18_10_1_6498 67 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 138 210 6 11 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 138 210 (Polychromatic418967fa.accept_20_5_18_10_1_3565 65 138 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 210 2 32 69 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 138 210 3 21 46 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 138 210 2 31 69
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 210
  (Polychromatic418967fa.accept_19_4_5_1_1_4077 61 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 210 6 10 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 210 (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 138 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 210 2 29 69 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 138 210 3 19 46 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 138 210 2 28 69 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 210
  (Polychromatic418967fa.accept_17_4_2_6_1_2629 55 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 210 6 9 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 138 210 (Polychromatic418967fa.accept_19_15_5_1_1_5360 53 138 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 210 2 26 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 138 210 3 17 46 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 138 210 2 25 69 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 210
  (Polychromatic418967fa.accept_11_5_6_1_1_988 49 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 210 6 8 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 138 210 (Polychromatic418967fa.accept_17_13_2_6_1_3683 47 138 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 210 2 23 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 138 210 3 15 46 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 138 210 2 22 69 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 210
  (Polychromatic418967fa.accept_27_16_3_21_1_12430 43 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 138 210 6 7 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 138 210 (Polychromatic418967fa.accept_19_3_5_1_1_6811 41 138 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 210 2 20 69 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 138 210 3 13 46 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 138 210 2 19 69 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 210
  (Polychromatic418967fa.accept_19_18_5_1_1_8255 37 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 210 6 6 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 138 210 (Polychromatic418967fa.accept_17_1_2_6_1_818 35 138 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 210 2 17 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 138 210 3 11 46 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 210 2 16 69 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 210
  (Polychromatic418967fa.accept_19_12_5_1_1_11093 31 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 138 210 6 5 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 138 210 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 138 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 210 2 14 69 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 210 3 9 46 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 210 2 13 69 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 210
  (Polychromatic418967fa.accept_19_6_5_1_1_2765 25 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 210 6 4 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 210 (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 138 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 210 2 11 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 210 3 7 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 210 2 10 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 210
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 210 6 3 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 210 (Polychromatic418967fa.accept_20_17_18_10_1_5046 17 138 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 210 2 8 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 210 3 5 46 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 210 2 7 69 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 210
  (Polychromatic418967fa.accept_17_13_2_6_1_3683 13 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 210 6 2 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 138 210 (Polychromatic418967fa.accept_27_11_3_21_1_12429 11 138 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 210 2 5 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 138 210 3 3 46 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 138 210 2 4 69 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 210
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 210 6 1 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 210 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 138 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 210 2 2 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 210 3 1 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 210 2 1 69 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 210 (Polychromatic418967fa.accept_17_1_2_6_1_818 1
  138 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 137 210 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 137 210 (accept_3_4 73 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 137 210 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 137 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 137 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 210 (accept_3_4 70 137 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 210 (Polychromatic418967fa.accept_9_6_2_3_1_771
  69 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 68 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 210 (accept_3_4 67 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 210 (Polychromatic418967fa.accept_23_20_22_3_1_12393 66 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 210 (Polychromatic418967fa.accept_16_1_9_2_1_4161 65 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 210 (accept_3_4 64 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 137 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 62 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 210 (accept_3_4 61 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 210 (accept_3_4 58 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 210 (Polychromatic418967fa.accept_13_5_7_2_1_852 57 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 210
  (Polychromatic418967fa.accept_17_5_1_6_1_2615 56 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 210 (accept_3_4 55 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 210 (Polychromatic418967fa.accept_16_6_9_2_1_6518 54 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 210 (accept_3_4 52 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 210 (accept_3_4 49 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 210 (Polychromatic418967fa.accept_13_9_7_2_1_3869 48 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 210 (accept_3_4 46 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 210 (Polychromatic418967fa.accept_18_9_11_12_1_5727 45 137 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 210 (accept_3_4 43 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 210 (accept_3_4 40 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 210
  (Polychromatic418967fa.accept_16_6_9_2_1_6518 38 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 210 (accept_3_4 37 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 210 (Polychromatic418967fa.accept_17_2_1_6_1_3777 36 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 210 (accept_3_4 34 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 210 (accept_3_4 31 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 210 (Polychromatic418967fa.accept_23_7_22_3_1_10751 30 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 210 (Polychromatic418967fa.accept_17_12_1_6_1_3680 29 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 210 (accept_3_4 28 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 210 (accept_3_4 25 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 210 (accept_3_4 22 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 210 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 210
  (Polychromatic418967fa.accept_17_3_1_6_1_251 20 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 210 (accept_3_4 19 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 210 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 210 (accept_3_4 16 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 210 (accept_3_4 13 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 210 (Polychromatic418967fa.accept_16_12_9_2_1_8989 12 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 210 (accept_3_4 10 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 210 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 210 (accept_3_4 7 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 210 (accept_3_4 4 137 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 210
  (Polychromatic418967fa.accept_17_2_1_6_1_3777 2 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 210 (accept_3_4 1 137 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 136 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 136 210 2 37 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 136 210 (Polychromatic418967fa.accept_13_8_6_2_1_865 73 136 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 136 210 2 36 68 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 136 210 (accept_3_5 71 136 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 136 210 2 35 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 136 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 136 210 2 34 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 136 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 136 210 2 33 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 136 210 (accept_3_5 65 136 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 136 210 2 32 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 136 210 (Polychromatic418967fa.accept_11_8_4_1_1_1000
  63 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 136 210 2 31 68 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 136 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 61 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 136 210 2 30 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 136 210 (accept_3_5 59 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 136 210 2 29 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 136 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 210 2 28 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 210
  (Polychromatic418967fa.accept_19_17_3_1_1_4056 55 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 210 2 27 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 210 (accept_3_5 53 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 210 2 26 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 210 2 25 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 210 2 24 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 136 210 (accept_3_5 47 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 136 210 2 23 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 136 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 210 2 22 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 210 2 21 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 210 (accept_3_5 41 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 210 2 20 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 210 2 19 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 210
  (Polychromatic418967fa.accept_25_12_11_10_1_12428 37 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 136 210 2 18 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 136 210 (accept_3_5 35 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 136 210 2 17 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 136 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 210 2 16 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 136 210 2 15 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 136 210 (accept_3_5 29 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 136 210 2 14 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 136 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 210 2 13 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 210 2 12 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 210 (accept_3_5 23 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 210 2 11 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 210 2 10 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 210
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 210 2 9 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 136 210 (accept_3_5 17 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 210 2 8 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 136 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 210 2 7 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 210 2 6 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 136 210 (accept_3_5 11 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 136 210 2 5 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 136 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 136 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 210 2 4 68 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 210 2 3 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 210 (accept_3_5 5 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  210 2 2 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 136 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 210 2 1 68 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 136 210 (Polychromatic418967fa.accept_13_1_6_2_1_377 1 136 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 135 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 135 210 15 5 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 135 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 74 135 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 73
  135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 135 210 3 24 45 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 135 210
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 71 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 135 210 5 14 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 135 210 3 23 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 135 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 68 135 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 210
  (Polychromatic418967fa.accept_20_7_15_10_1_3628 67 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 135 210 3 22 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 135 210 5 13 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 135 210 (Polychromatic418967fa.accept_12_4_3_6_1_879 64 135 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 135 210 3 21 45 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 135 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 62 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 135 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 210 15 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 210 (Polychromatic418967fa.accept_13_7_5_2_1_401
  59 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 210
  (Polychromatic418967fa.accept_12_10_3_6_1_882 58 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 135 210 3 19 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 135 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 135 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 135 210 5 11 27 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 135 210 3 18 45 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 135 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 210 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 135 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 135 210 3 17 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 135 210 5 10 27 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 135 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 135 210 3 16 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 135 210 (Polychromatic418967fa.accept_18_11_9_12_1_4427 47 135 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 210
  (Polychromatic418967fa.accept_11_2_3_1_1_244 46 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 135 210 15 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 135 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 135 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 210 (Polychromatic418967fa.accept_13_4_5_2_1_1436 43 135
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 135 210 3 14 45 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 135 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 135 210 5 8 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 135 210 3 13 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 135 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 38 135 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 135 210 3 12 45 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 135 210 5 7 27 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 210
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 135 210 3 11 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 135 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 135 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 210
  (Polychromatic418967fa.accept_19_12_2_1_1_12338 31 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 135 210 15 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 135 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 210
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 210 3 9 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 135 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 135 210 5 5 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 135 210 3 8 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 210 (Polychromatic418967fa.accept_13_10_5_2_1_1477
  23 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 210
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 135 210 3 7 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 135 210 5 4 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 135 210 (Polychromatic418967fa.accept_20_19_15_10_1_8044 19 135 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 210 3 6 45 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 210 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 135 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 210 15 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 210 (Polychromatic418967fa.accept_12_2_3_6_1_112
  14 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 135 210 3 4 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 135 210 (Polychromatic418967fa.accept_16_11_7_2_1_4185 11 135 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 135 210 5 2 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 135 210 3 3 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 8
  135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 210
  (Polychromatic418967fa.accept_13_7_5_2_1_401 7 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 135 210 3 2 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 135 210 5 1 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 135 210 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 135 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 210 3 1 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 135 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135 210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 134 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 134 210 2 38 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 75 134 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 134 210 2 37 67 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 134 210 (accept_3_4 73
  134 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 134 210 2 36 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 134 210
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 71 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 134 210 2 35 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 134 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 134 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 134 210 2 34 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 134 210 (accept_3_4 67 134 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 134 210 2 33 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 134 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 65
  134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 210 2 32 67 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 134 210 2 31 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 134 210 (accept_3_4 61 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 210 2 30 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 134 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 210 2 29 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 210 2 28 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 210 (accept_3_4 55 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 210 2 27 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 210 (Polychromatic418967fa.accept_23_7_19_3_1_12427 53 134 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 210 2 26 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 210 2 25 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 210 (accept_3_4 49 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 210 2 24 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 134 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 210 2 23 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 210 2 22 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 210 (accept_3_4 43 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 210 2 21 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 134 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 210 2 20 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 210 2 19 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 210 (accept_3_4 37 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 210 2 18 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 210 (Polychromatic418967fa.accept_16_3_6_2_1_4157 35 134 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 210 2 17 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 210 2 16 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 210 (accept_3_4 31 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 210 2 15 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 134 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 210 2 14 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 210 2 13 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 210 (accept_3_4 25 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 210 2 12 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 134 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 210 2 11 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 210
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 210 2 10 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 210 (accept_3_4 19 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 210 2 9 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 210 (Polychromatic418967fa.accept_16_1_6_2_1_3100 17 134 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 210 2 8 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 210 2 7 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 210 (accept_3_4 13 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 210 2 6 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 134 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 210 2 5 67 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 210 2 4 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 210 (accept_3_4 7 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  210 2 3 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 134 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 210 2 2 67 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 210 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 134 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 210 2 1 67 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 210 (accept_3_4 1 134 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 133 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 133 210 7 11 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 133 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 210 (accept_3_5 74 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 210 (Polychromatic418967fa.accept_20_12_13_10_1_8061 72 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 210 (accept_3_5 71 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 133 210 7 10 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 133 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 69
  133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 210 (accept_3_5 68
  133 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 133 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 133 210 (Polychromatic418967fa.accept_13_1_3_2_1_1429 66 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 210 (accept_3_5 65 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 133 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 133 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 133 210 7 9 19 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 133 210 (accept_3_5 62 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 133 210 (Polychromatic418967fa.accept_13_9_3_2_1_399 61 133
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 210
  (Polychromatic418967fa.accept_9_6_7_3_1_436 60 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 133 210 (accept_3_5 59 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 133 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 133 210 (Polychromatic418967fa.accept_13_5_3_2_1_1499 57 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 133 210 7 8 19 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 133 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 133 210 (Polychromatic418967fa.accept_17_3_14_6_1_3742 54 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 210 (accept_3_5 53 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 133 210 (Polychromatic418967fa.accept_20_12_13_10_1_8061 52 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 210 (accept_3_5 50 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49
  133 210 7 7 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  48 133 210 (Polychromatic418967fa.accept_13_9_3_2_1_399 48 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 133 210 (accept_3_5 47 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 133 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 210 (Polychromatic418967fa.accept_16_13_5_2_1_2131 45 133
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 210 (accept_3_5 44 133
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 133 210 7 6 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 133 210 (accept_3_5 41 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 133 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 210 (accept_3_5 38 133 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 210
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 133 210 7 5 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 133 210 (Polychromatic418967fa.accept_25_9_8_10_1_12426 34 133 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 210 (Polychromatic418967fa.accept_9_6_7_3_1_436
  33 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 210 (accept_3_5 32
  133 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 133 210 (Polychromatic418967fa.accept_22_8_1_12_1_7506 30 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 210 (accept_3_5 29 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 133 210 7 4 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 133 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 210 (accept_3_5 26 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 210 (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 133
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 210
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 210 (accept_3_5 23 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 133 210 7 3 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 133 210 (accept_3_5 20 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 133 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 210 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 133
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 210 (accept_3_5 17 133
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 210
  (Polychromatic418967fa.accept_22_16_1_12_1_12425 16 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 133 210 7 2 19 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 133 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 133 210 (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 210 (accept_3_5 11 133 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 133 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 133 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 210 (Polychromatic418967fa.accept_13_9_3_2_1_399 9
  133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 210 (accept_3_5 8 133
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 133 210 7 1 19 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 133 210
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 210 (accept_3_5 5 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 133 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 210 (accept_3_5 2 133 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 133 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 132 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 132 210 6 13 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 132 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 132 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 210 2 38 66 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 132 210 3 25 44 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 132 210 2 37 66 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 73 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 210 6 12 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 71 132 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 210 2 35 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 132 210 3 23 44 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 132 210 2 34 66 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 210 6 11 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 65 132 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 210 2 32 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 132 210 3 21 44 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 132 210 2 31 66 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 210 6 10 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 132 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 210 2 29 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 132 210 3 19 44 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 132 210 2 28 66 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 55 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 210 6 9 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 132 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 132 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 210 2 26 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 132 210 3 17 44 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 132 210 2 25 66 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 210 6 8 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 132 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 132 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 210 2 23 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 132 210 3 15 44 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 132 210 2 22 66 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 210 6 7 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 132 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 132 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 210 2 20 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 132 210 3 13 44 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 210 2 19 66 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 210 6 6 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 132 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 210 2 17 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 132 210 3 11 44 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 210 2 16 66 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 210 6 5 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 132 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 132 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 210 2 14 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 132 210 3 9 44 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 132 210 2 13 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 210 6 4 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 132 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 210 2 11 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 210 3 7 44 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 132 210 2 10 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 210 6 3 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 132 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 210 2 8 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 210 3 5 44 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 210 2 7 66 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 210 6 2 22 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 132 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 210 2 5 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 132 210 3 3 44 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 132 210 2 4 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 7
  132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 210 6 1 22 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 210
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 132 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 132 210 2 2 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 132 210 3 1 44 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 132 210 2 1 66 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 132 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 132 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 131 210 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 131 210 (accept_3_4 79 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 131 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 131 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 131 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 210 (accept_3_4 76 131 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 210 (Polychromatic418967fa.accept_11_9_10_1_1_581
  75 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 74 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 210 (accept_3_4 73 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 210 (Polychromatic418967fa.accept_19_15_17_1_1_8225 72 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 210 (accept_3_4 70 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 210
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 68 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 210 (accept_3_4 67 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 210 (Polychromatic418967fa.accept_19_9_17_1_1_8325 66 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 210 (accept_3_4 64 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 210 (Polychromatic418967fa.accept_16_15_3_2_1_4170 63 131 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 210 (accept_3_4 61 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 210 (Polychromatic418967fa.accept_20_19_11_10_1_3615 59 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 210 (accept_3_4 58 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 131 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 210 (accept_3_4 55 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 210 (Polychromatic418967fa.accept_16_6_3_2_1_3096 54 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 210 (accept_3_4 52 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 210
  (Polychromatic418967fa.accept_24_2_11_18_1_131 50 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 210 (accept_3_4 49 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 210 (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 210 (accept_3_4 46 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 44 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 210 (accept_3_4 43 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 210 (accept_3_4 40 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 210 (Polychromatic418967fa.accept_20_19_11_10_1_3615 39 131 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 210 (accept_3_4 37 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 210 (Polychromatic418967fa.accept_17_2_12_6_1_3737 36 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 210 (accept_3_4 34 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 210
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 32 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 210 (accept_3_4 31 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 210 (Polychromatic418967fa.accept_22_8_21_12_1_7604 30 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 210 (accept_3_4 28 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 210 (Polychromatic418967fa.accept_17_10_12_6_1_4917 27 131 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 210 (accept_3_4 25 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 210 (Polychromatic418967fa.accept_19_4_17_1_1_4009 23 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 210 (accept_3_4 22 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 210 (accept_3_4 19 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 210 (Polychromatic418967fa.accept_17_1_12_6_1_3735 18 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 210 (accept_3_4 16 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 210
  (Polychromatic418967fa.accept_19_14_17_1_1_2788 14 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 210 (accept_3_4 13 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 210 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 131 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 131 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 210 (accept_3_4 10 131 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 210 (accept_3_4 7 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 210 (accept_3_4 4 131 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 210 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 131 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 210 (accept_3_4 1 131 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 130 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 130 210 10 8 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 130 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 79 130 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 130 210 2 39 65 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 130 210 (accept_3_5 77 130 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 130 210 2 38 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 130 210 5 15 26 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 130 210 2 37 65 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 73 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 130 210 2 36 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 130 210 (accept_3_5 71 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 210 10 7 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 130 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 210 2 34 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 210
  (Polychromatic418967fa.accept_19_10_16_1_1_8271 67 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 130 210 2 33 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 130 210 5 13 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 130 210 2 32 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 130 210 (Polychromatic418967fa.accept_12_3_10_6_1_442
  63 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 210 2 31 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 61 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 210 10 6 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 210 (accept_3_5 59 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 210 2 29 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 130 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 210 2 28 65 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 130 210 5 11 26 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 130 210 2 27 65 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 130 210
  (accept_3_5 53 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 130 210 2 26 65 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 130 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 51 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 130 210 10 5 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 130 210 (Polychromatic418967fa.accept_28_21_18_14_1_10476 49 130 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 130 210 2 24 65 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 130 210 (accept_3_5 47 130 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 130 210 2 23 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 130 210 5 9 26 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 130 210 2 22 65 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 210 2 21 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 210 (accept_3_5 41 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 210 10 4 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 130 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 210 2 19 65 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 210 2 18 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 130 210 5 7 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 130 210 2 17 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 130 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 130 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 210 2 16 65 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 210
  (Polychromatic418967fa.accept_22_9_20_12_1_12407 31 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 130 210 10 3 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 130 210 (accept_3_5 29 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 210 2 14 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 130 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 210 2 13 65 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 130 210 5 5 26 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 130 210 2 12 65 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 210 (accept_3_5 23
  130 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 210 2 11 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 210
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 130 210 10 2 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 130 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 130 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 130 210 2 9 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 130 210 (accept_3_5 17 130 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 130 210 2 8 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 130 210 5 3 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 130 210 2 7 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 210
  (Polychromatic418967fa.accept_17_13_11_6_1_4837 13 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 130 210 2 6 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 130 210 (accept_3_5 11 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 210 10 1 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 130 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 130 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 210 2 4 65 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 210 2 3 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 130 210 5 1 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 130 210 2 2 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 130 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 130 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 210 2 1 65 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  130 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 129 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 129 210 3 27 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 129 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 80 129 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 129 210 3 26 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 129 210 (Polychromatic418967fa.accept_20_17_9_10_1_12382 77 129 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 76 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 129 210 3 25 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 129 210 (Polychromatic418967fa.accept_12_2_9_6_1_439 74 129 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 210 (Polychromatic418967fa.accept_16_9_1_2_1_2126
  73 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 129 210 3 24 43 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 129 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 210 (Polychromatic418967fa.accept_11_4_8_1_1_1047 70 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 129 210 3 23 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 129 210 (Polychromatic418967fa.accept_12_8_9_6_1_127
  68 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 129 210 3 22 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 129 210 (Polychromatic418967fa.accept_19_8_15_1_1_3979 65 129 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 64 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 129 210 3 21 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 129 210 (Polychromatic418967fa.accept_12_2_9_6_1_439 62 129 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 210
  (Polychromatic418967fa.accept_18_7_3_12_1_3241 61 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 129 210 3 20 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 129 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 129 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 129 210 3 19 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 129 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 129 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 129 210 3 18 43 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 129 210
  (Polychromatic418967fa.accept_13_1_12_2_1_384 53 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 129 210 3 17 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 129 210 (Polychromatic418967fa.accept_12_2_9_6_1_439
  50 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 210
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 49 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 129 210 3 16 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 129 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 129 210 3 15 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 129 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 129 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 210 3 14 43 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 210
  (Polychromatic418967fa.accept_16_9_1_2_1_2126 41 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 129 210 3 13 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 129 210 (Polychromatic418967fa.accept_12_2_9_6_1_439
  38 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 210
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 129 210 3 12 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 129 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 129 210 3 11 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 129 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 129 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 210 3 10 43 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 210
  (Polychromatic418967fa.accept_13_3_12_2_1_385 29 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 210 3 9 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 210 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  26 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 210
  (Polychromatic418967fa.accept_16_9_1_2_1_2126 25 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 129 210 3 8 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 129 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 210 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 129
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 210 3 7 43 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 210
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 210 3 6 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 210 (Polychromatic418967fa.accept_13_4_12_2_1_1459
  17 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 129 210 3 5 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 129 210 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 210 (Polychromatic418967fa.accept_18_13_3_12_1_3207 13 129
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 210 3 4 43 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 210 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 210 3 3 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 129 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 129 210 3 2 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 129 210 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 210 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 129 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 210 3 1 43 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 210
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 129 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 210 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 129 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 128 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 128 210 2 41 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 128 210 (Polychromatic418967fa.accept_12_9_8_6_1_466 81 128 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 128 210 2 40 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 128 210 (accept_3_4 79 128 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 128 210 2 39 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 128 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 128 210 2 38 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 128 210 (Polychromatic418967fa.accept_12_3_8_6_1_895 75 128 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 128 210 2 37 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 128 210 (accept_3_4 73 128 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 128 210 2 36 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 128 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 71
  128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 210 2 35 64 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 69 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 210 2 34 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 210 (accept_3_4 67 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 210 2 33 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 210 (Polychromatic418967fa.accept_20_5_8_10_1_11026 65 128 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 210 2 32 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 128 210 2 31 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 210 (accept_3_4 61 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 210 2 30 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 128 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 210 2 29 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 210 2 28 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 210 (accept_3_4 55 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 210 2 27 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 128 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 210 2 26 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 210 2 25 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 210 (accept_3_4 49 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 210 2 24 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 210 (Polychromatic418967fa.accept_19_9_14_1_1_6792 47 128 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 210 2 23 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 210 2 22 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 210 (accept_3_4 43 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 210 2 21 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 128 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 210 2 20 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 210
  (Polychromatic418967fa.accept_11_6_7_1_1_564 39 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 210 2 19 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 210 (accept_3_4 37 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 210 2 18 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 128 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 210 2 17 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 210 2 16 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 128 210 (accept_3_4 31 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 210 2 15 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 210 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 128 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 210 2 14 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 210 2 13 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 210 (accept_3_4 25 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 210 2 12 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 128 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 210 2 11 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 210 2 10 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 210 (accept_3_4 19 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 210 2 9 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 128 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 128 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 210 2 8 64 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 128 210 2 7 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 128 210 (accept_3_4 13 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 128 210 2 6 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 128 210 (Polychromatic418967fa.accept_22_11_18_12_1_7659 11 128 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 210 2 5 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 210 2 4 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 210 (accept_3_4 7 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  210 2 3 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 128 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 210 2 2 64 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 128 210 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 128 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 210 2 1 64 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 210 (accept_3_4 1 128 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 127 210 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 127 210 (accept_3_5 83 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 127 210 (Polychromatic418967fa.accept_11_5_6_1_1_988 82 127 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 127 210 (accept_3_5 80 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 127 210 (Polychromatic418967fa.accept_9_7_1_3_1_443
  79 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 78 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 127 210 (accept_3_5 77 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 127 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 127 210 (Polychromatic418967fa.accept_18_3_1_12_1_4419 75 127 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 210 (accept_3_5 74 127 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 210
  (Polychromatic418967fa.accept_22_6_17_12_1_7704 72 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 127 210 (accept_3_5 71 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 127 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 127 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 210 (accept_3_5 68 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 210 (Polychromatic418967fa.accept_9_4_1_3_1_190
  67 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 210
  (Polychromatic418967fa.accept_17_15_8_6_1_8733 66 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 127 210 (accept_3_5 65 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 127 210 (Polychromatic418967fa.accept_13_12_10_2_1_1451 64 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 210 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 127 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 210 (accept_3_5 62 127 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 60 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 210 (accept_3_5 59 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 210 (accept_3_5 56 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 210 (Polychromatic418967fa.accept_13_3_10_2_1_381 55 127 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 210
  (Polychromatic418967fa.accept_19_16_13_1_1_12406 54 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 127 210 (accept_3_5 53 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 127 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 127 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 210 (accept_3_5 50 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 210
  (Polychromatic418967fa.accept_17_14_8_6_1_2643 48 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 210 (accept_3_5 47 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 210 (Polychromatic418967fa.accept_19_8_13_1_1_8221 46 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 210 (accept_3_5 44 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 127 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 210 (accept_3_5 41 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 210 (Polychromatic418967fa.accept_18_3_1_12_1_4419 39 127 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 210 (accept_3_5 38 127 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 210
  (Polychromatic418967fa.accept_22_14_17_12_1_5950 36 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 127 210 (accept_3_5 35 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 127 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 127 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 210 (accept_3_5 32 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 210 (Polychromatic418967fa.accept_9_4_1_3_1_190
  31 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 210
  (Polychromatic418967fa.accept_24_6_7_18_1_12424 30 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 127 210 (accept_3_5 29 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 127 210 (Polychromatic418967fa.accept_16_12_15_2_1_6473 28 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 210 (Polychromatic418967fa.accept_11_5_6_1_1_988
  27 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 210 (accept_3_5 26
  127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 127 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 127 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 210 (accept_3_5 23 127 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 127 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 210 (accept_3_5 20
  127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 210
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 19 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 127 210 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 127 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 210 (accept_3_5 17 127 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 127 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 210 (Polychromatic418967fa.accept_9_6_1_3_1_191
  15 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 210 (accept_3_5 14
  127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 127 210 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 210 (accept_3_5 11 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 210 (Polychromatic418967fa.accept_19_10_13_1_1_8264 10 127 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 210 (accept_3_5 8 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 210 (accept_3_5 5 127 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 127 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 210
  (Polychromatic418967fa.accept_13_3_10_2_1_381 3 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 210 (accept_3_5 2 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 126 210 (Eq.refl Bool.true) (allA_succ_of_gcd 84 126 210 42 2 3 5 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 210
  (Polychromatic418967fa.accept_11_6_5_1_1_586 83 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 126 210 2 41 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 126 210 3 27 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 126 210 2 40 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 210 (Polychromatic418967fa.accept_13_1_9_2_1_1448 79 126
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 126 210 6 13 21 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 126 210 7 11 18 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 126 210 2 38 63
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 126 210 3 25
  42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 126 210 2
  37 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126
  210 (Polychromatic418967fa.accept_22_7_16_12_1_7702 73 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 126 210 6 12 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 126 210 (Polychromatic418967fa.accept_13_6_9_2_1_838 71 126 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 210 14 5 9 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 126 210 3 23 42 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 126 210 2 34 63 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 210
  (Polychromatic418967fa.accept_17_16_7_6_1_7343 67 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 210 6 11 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 210 (Polychromatic418967fa.accept_17_14_7_6_1_11222 65 126 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 210 2 32 63 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 126 210 21 3 6 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 126 210 2 31 63 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 210
  (Polychromatic418967fa.accept_11_6_5_1_1_586 61 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 210 6 10 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 210 (Polychromatic418967fa.accept_13_7_9_2_1_2167 59 126 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 210 2 29 63 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 126 210 3 19 42 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 126 210 14 4 9 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 210
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 210 6 9 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 126 210 (Polychromatic418967fa.accept_13_1_9_2_1_1448 53 126 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 210 2 26 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 126 210 3 17 42 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 126 210 2 25 63 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 126 210 7 7 18 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 126 210 6 8 21 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 210
  (Polychromatic418967fa.accept_17_13_7_6_1_827 47 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 210 2 23 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 126 210 3 15 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 210 2 22 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 210 (Polychromatic418967fa.accept_19_5_12_1_1_2817 43 126
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 210 42 1 3 5 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 210
  (Polychromatic418967fa.accept_22_19_16_12_1_7588 41 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 126 210 2 20 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 126 210 3 13 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 210 2 19 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 210 (Polychromatic418967fa.accept_13_11_9_2_1_2969
  37 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 210 6 6 21 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 126 210 7 5 18 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 126 210 2 17 63
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 210 3 11
  42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 210 2
  16 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126
  210 (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 126 210 6 5 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 126 210 (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 126 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 210 14 2 9 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 210 3 9 42 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 210 2 13 63 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 210
  (Polychromatic418967fa.accept_20_5_6_10_1_3536 25 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 210 6 4 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 126 210 (Polychromatic418967fa.accept_19_4_12_1_1_3991 23 126 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 210 2 11 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 210 21 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 210 2 10 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 210
  (Polychromatic418967fa.accept_13_6_9_2_1_838 19 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 210 6 3 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 210 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 126 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 210 2 8 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 210 3 5 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 210 14 1 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 210 (Polychromatic418967fa.accept_17_13_7_6_1_827
  13 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 210 6 2 21 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 210
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 210 2 5 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 126 210 3 3 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 126 210 2 4 63 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 126 210 7 1 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 126 210 6 1 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 126 210 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 126 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 210 2 2 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 210 3 1 42 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 210 2 1 63 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 210
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 126 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86
  125 210 (Eq.refl Bool.true) (allA_succ_of_gcd 85 125 210 5 17 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 125 210 (Polychromatic418967fa.accept_13_6_8_2_1_1484 84 125
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 210 (accept_3_4 82 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 210 (Polychromatic418967fa.accept_18_9_17_12_1_462 81 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 125 210 5 16 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 125 210 (accept_3_4 79 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 125 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 125 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 125 210 (accept_3_4 76 125 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 125 210 5 15 25 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 125 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 74 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 125 210 (accept_3_4 73 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 125 210 (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 125 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 125 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 125 210 5 14 25 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 125 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 69 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 125 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 68 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 210 (accept_3_4 67 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 125 210 (Polychromatic418967fa.accept_19_9_11_1_1_8239 66 125 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 125 210 5 13 25 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 125 210 (accept_3_4 64 125 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 63
  125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 210
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 62 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 125 210 (accept_3_4 61 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  125 210 5 12 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 125 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 210 (accept_3_4 58 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 125 210 (Polychromatic418967fa.accept_20_17_5_10_1_3591 57 125 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 125 210 5 11 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 125 210 (Polychromatic418967fa.accept_20_14_5_10_1_3647 54 125 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 210
  (Polychromatic418967fa.accept_16_5_13_2_1_2138 53 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 210 (accept_3_4 52 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 125 210 5 10 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 125 210 (accept_3_4 49 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 125 210 (Polychromatic418967fa.accept_19_10_11_1_1_8318 48 125 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 210 (accept_3_4 46
  125 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 125 210 5 9 25 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 125 210
  (Polychromatic418967fa.accept_19_6_11_1_1_6815 44 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 210 (accept_3_4 43 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 125 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 125 210 5 8 25 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 125 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 125 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 210 (accept_3_4 37 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 125 210 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 125 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 125 210 5 7 25 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 125 210 (accept_3_4 34 125 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 210 (Polychromatic418967fa.accept_9_6_8_3_1_183
  33 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 210
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 210 (accept_3_4 31 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  125 210 5 6 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 125 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 125 210 (accept_3_4 28 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 125 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 210 (Polychromatic418967fa.accept_20_6_5_10_1_3531 26 125
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 125 210 5 5 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 125 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 24 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 210 (accept_3_4 22 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 210 (Polychromatic418967fa.accept_16_5_13_2_1_2138 21 125 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 210 5 4 25 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 210 (accept_3_4 19 125 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 210
  (Polychromatic418967fa.accept_19_18_11_1_1_4035 18 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 210 (Polychromatic418967fa.accept_20_17_5_10_1_3591 17 125 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 210 (accept_3_4 16 125 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 125 210 5 3 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 125 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 14
  125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 210 (accept_3_4 13
  125 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 210
  (Polychromatic418967fa.accept_19_12_11_1_1_4036 12 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 125 210 5 2 25 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 125 210
  (Polychromatic418967fa.accept_18_9_17_12_1_462 9 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 210 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 210 (accept_3_4 7 125 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 125 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 210 5 1 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 210 (accept_3_4 4 125 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 210 (accept_3_4 1 125 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 124 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 124 210 2 43 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 124 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 85 124 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 124 210 2 42 62 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 124 210 (accept_3_5 83
  124 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 124 210 2 41 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 124 210
  (Polychromatic418967fa.accept_12_9_4_6_1_460 81 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 124 210 2 40 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 124 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 79 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 124 210 2 39 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 124 210 (accept_3_5 77 124 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 124 210 2 38 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 124 210 (Polychromatic418967fa.accept_12_3_4_6_1_434
  75 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 124 210 2 37 62 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 124 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 73 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 124 210 2 36 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 124 210 (accept_3_5 71 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 124 210 2 35 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 124 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 124 210 2 34 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 124 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 67 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 124 210 2 33 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 124 210 (accept_3_5 65 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 124 210 2 32 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 124 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 210 2 31 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 210
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 61 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 210 2 30 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 210 (accept_3_5 59 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 210 2 29 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 210 2 28 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 55 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 210 2 27 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 210 (accept_3_5 53 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 210 2 26 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 210 2 25 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 210 2 24 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 210 (accept_3_5 47 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 210 2 23 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 210 2 22 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 210
  (Polychromatic418967fa.accept_25_18_24_10_1_3328 43 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 124 210 2 21 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 124 210 (accept_3_5 41 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 210 2 20 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 210 2 19 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 210 2 18 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 124 210 (accept_3_5 35 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 124 210 2 17 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 124 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 210 2 16 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 210 2 15 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 210 (accept_3_5 29 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 210 2 14 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 210 2 13 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 210
  (Polychromatic418967fa.accept_16_9_12_2_1_3093 25 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 210 2 12 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 210 (accept_3_5 23 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 210 2 11 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 210 2 10 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 210 2 9 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 124 210 (accept_3_5 17 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 124 210 2 8 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 124 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 210 2 7 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 210 2 6 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 124 210 (accept_3_5 11 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 124 210 2 5 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 124 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 124 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 210 2 4 62 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 210
  (Polychromatic418967fa.accept_16_7_12_2_1_8902 7 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 124 210 2 3 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 210 (accept_3_5 5 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  210 2 2 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 124 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 210 2 1 62 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 124 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 124 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 123 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 123 210 3 29 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 123 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 86 123 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 85 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 123 210 3 28 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 123 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 83 123 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 210 (Polychromatic418967fa.accept_9_1_6_3_1_177
  82 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 123 210 3 27 41 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 123 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 80 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 123 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 79 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 123 210 3 26 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 77
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 76 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 123 210 3 25 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 123 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 74 123 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 73
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 123 210 3 24 41 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 123 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 71 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 70 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 123 210 3 23 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 123 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 68
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 123 210 3 22 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 123 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 210 (Polychromatic418967fa.accept_9_1_6_3_1_177
  64 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 123 210 3 21 41 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 123 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 62 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 123 210 3 20 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 123 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 123 210 3 19 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 123 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 123 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 210 (Polychromatic418967fa.accept_9_1_6_3_1_177
  55 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 123 210 3 18 41 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 123 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 123 210 3 17 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 123 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 50
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 123 210 3 16 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 123 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 123 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 210 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 123 210 3 15 41 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 123 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 123 210 3 14 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 41
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 123 210 3 13 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 123 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 123 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 210 3 12 41 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 123 210 3 11 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 123 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 210 3 10 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 210 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 210 3 9 41 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 210 3 8 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 123 210 3 7 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 123 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 123 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 210 3 6 41 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 210 3 5 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 123 210 3 4 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 123 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 123 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 210 3 3 41 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 210 3 2 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 123 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 210 3 1 41 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 123 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 122 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 122 210 2 44 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 87 122 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 122 210 2 43 61 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 122 210 (accept_3_4 85
  122 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 122 210 2 42 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 122 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 83 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 122 210 2 41 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 122 210 (Polychromatic418967fa.accept_12_9_2_6_1_455 81 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 122 210 2 40 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 122 210 (accept_3_4 79 122 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 122 210 2 39 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 122 210 (Polychromatic418967fa.accept_13_12_5_2_1_2173
  77 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 210 2 38 61 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 75 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 210 2 37 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 210 (accept_3_4 73 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 210 2 36 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 210 2 35 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 69 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 210 2 34 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 210 (accept_3_4 67 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 210 2 33 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 65 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 210 2 32 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 210 2 31 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 210 (accept_3_4 61 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 210 2 30 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 210 (Polychromatic418967fa.accept_13_7_5_2_1_401 59 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 210 2 29 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 210 2 28 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 210 (accept_3_4 55 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 210 2 27 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 210 2 26 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 51 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 210 2 25 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 210 (accept_3_4 49 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 210 2 24 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 210 2 23 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 210 2 22 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 210 (accept_3_4 43 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 210 2 21 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 210 (Polychromatic418967fa.accept_25_16_22_10_1_6927 41 122 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 210 2 20 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 210 2 19 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 210 (accept_3_4 37 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 210 2 18 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 210 2 17 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 210 2 16 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 210 (accept_3_4 31 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 210 2 15 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 210 2 14 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 210 2 13 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 210 (accept_3_4 25 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 210 2 12 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 210 (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 122 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 210 2 11 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 210 2 10 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 210 (accept_3_4 19 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 210 2 9 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 210 2 8 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 210 2 7 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 210 (accept_3_4 13 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 210 2 6 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 122 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 210 2 5 61 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 210 2 4 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 210 (accept_3_4 7 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  210 2 3 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 210 (Polychromatic418967fa.accept_17_5_3_6_1_12347 5 122 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 210 2 2 61 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 122 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 210 2 1 61 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 210 (accept_3_4 1 122 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 121 210
  (Eq.refl Bool.true) (allA_succ_of_accept 89 121 210 (accept_3_5 89 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 121 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 121 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 121 210 (accept_3_5 86 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 121 210
  (Polychromatic418967fa.accept_20_5_1_10_1_6523 85 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 121 210 (Polychromatic418967fa.accept_13_6_4_2_1_1433 84 121 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 210 (accept_3_5 83 121 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 121 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 121 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 210 (Polychromatic418967fa.accept_16_1_9_2_1_4161
  81 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 210 (accept_3_5 80
  121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 121 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 121 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 121 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 210 (accept_3_5 77 121 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 121 210 (Polychromatic418967fa.accept_13_11_4_2_1_2954 76 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 210 (accept_3_5 74 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 210 (Polychromatic418967fa.accept_17_4_2_6_1_2629 72 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 210 (accept_3_5 71 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 69 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 210 (accept_3_5 68 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 210 (Polychromatic418967fa.accept_23_20_6_3_1_12331 66 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 210 (accept_3_5 65 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 210 (accept_3_5 62 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 121 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 210 (accept_3_5 59 121 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 210 (Polychromatic418967fa.accept_13_6_4_2_1_1433 58 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 210
  (Polychromatic418967fa.accept_13_5_4_2_1_846 57 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 210 (accept_3_5 56 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 210 (Polychromatic418967fa.accept_16_6_9_2_1_6518 54 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 210 (accept_3_5 53 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 210 (accept_3_5 50 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 210 (Polychromatic418967fa.accept_16_1_9_2_1_4161 49 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 210 (Polychromatic418967fa.accept_19_10_7_1_1_1685 48 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 210 (accept_3_5 47 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 210
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 210 (accept_3_5 44 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 121 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 210 (accept_3_5 41 121 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 210 (Polychromatic418967fa.accept_19_2_7_1_1_2808 40 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 210 (accept_3_5 38 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 210 (Polychromatic418967fa.accept_22_14_11_12_1_7644 36 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 210 (accept_3_5 35 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 210 (accept_3_5 32 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 210 (Polychromatic418967fa.accept_17_13_2_6_1_3683 30 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 210 (accept_3_5 29 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 210 (accept_3_5 26 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 121 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 210 (accept_3_5 23 121 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 210 (Polychromatic418967fa.accept_16_6_9_2_1_6518 22 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 210
  (Polychromatic418967fa.accept_17_4_2_6_1_2629 21 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 210 (accept_3_5 20 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 210 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 210 (accept_3_5 17 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 210 (accept_3_5 14 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 210 (Polychromatic418967fa.accept_17_13_2_6_1_3683 13 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 210 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 210 (accept_3_5 11 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 121 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 210
  (Polychromatic418967fa.accept_20_9_1_10_1_6466 9 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 210 (accept_3_5 8 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 121 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 210 (accept_3_5 5 121 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 210 (Polychromatic418967fa.accept_17_4_2_6_1_2629 4 121 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 210 (accept_3_5 2 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 121 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 120 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 120 210 30 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 120 210 (Polychromatic418967fa.accept_13_11_3_2_1_863 89 120 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 210 2 44 60 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 120 210 3 29 40 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 120 210 2 43 60 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 120 210 5 17 24
  42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 120 210 6 14
  20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 120 210
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 83 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 120 210 2 41 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 120 210 3 27 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 120 210 10 8 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 120 210 (Polychromatic418967fa.accept_11_2_10_1_1_1017 79 120
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 120 210 6 13 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 120 210
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 77 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 120 210 2 38 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 120 210 15 5 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 120 210 2 37 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 120 210 (Polychromatic418967fa.accept_17_5_1_6_1_2615 73 120 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 120 210 6 12 20 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 120 210
  (Polychromatic418967fa.accept_17_3_1_6_1_251 71 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 210 10 7 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 120 210 3 23 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 120 210 2 34 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 210 (Polychromatic418967fa.accept_19_10_6_1_1_6828 67 120
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 210 6 11 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 120 210 5 13 24 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 120 210 2 32 60
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 120 210 3 21
  40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 120 210 2
  31 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120
  210 (Polychromatic418967fa.accept_13_9_3_2_1_399 61 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 120 210 30 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 210 (Polychromatic418967fa.accept_19_2_6_1_1_9729 59 120 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 210 2 29 60 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 120 210 3 19 40 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 120 210 2 28 60 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 120 210 5 11 24
  42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 120 210 6 9 20
  35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 210
  (Polychromatic418967fa.accept_11_9_10_1_1_581 53 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 210 2 26 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 120 210 3 17 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 210 10 5 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 210 (Polychromatic418967fa.accept_13_10_3_2_1_4728 49 120
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 210 6 8 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 210
  (Polychromatic418967fa.accept_26_21_16_2_1_12423 47 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 120 210 2 23 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 210 15 3 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 210 2 22 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 210 (Polychromatic418967fa.accept_19_5_6_1_1_5366 43 120
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 210 6 7 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 210
  (Polychromatic418967fa.accept_19_3_6_1_1_4064 41 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 210 10 4 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 120 210 3 13 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 120 210 2 19 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 210 (Polychromatic418967fa.accept_13_11_3_2_1_863 37 120
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 210 6 6 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 210 5 7 24 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 120 210 2 17 60 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 210 3 11 40
  70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 210 2 16
  60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 210
  (Polychromatic418967fa.accept_11_9_10_1_1_581 31 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 210 30 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 210 (Polychromatic418967fa.accept_17_12_1_6_1_3680 29 120 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 210 2 14 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 210 3 9 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 210 2 13 60 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 210 5 5 24 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 210 6 4 20 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 210
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 210 2 11 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 120 210 3 7 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 120 210 10 2 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 120 210 (Polychromatic418967fa.accept_17_2_1_6_1_3777 19 120 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 210 6 3 20 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 210
  (Polychromatic418967fa.accept_27_17_12_21_1_12422 17 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 120 210 2 8 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 210 15 1 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 210 2 7 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 210 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 120
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 210 6 2 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 210
  (Polychromatic418967fa.accept_13_11_3_2_1_863 11 120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 210 10 1 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 120 210 3 3 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 120 210 2 4 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 120 210 (Polychromatic418967fa.accept_19_7_6_1_1_796 7 120 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 210 6 1 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 210 5 1 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 120 210 2 2 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 210 3 1 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 210 2 1 60 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 210 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1
  120 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 119 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 119 210 7 13 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 119 210 (Polychromatic418967fa.accept_25_15_19_10_1_12421 90
  119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 119 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 119 210 (accept_3_4 88 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 119 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 119 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 86 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 210 (accept_3_4 85 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 84 119 210 7 12 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 119 210 (Polychromatic418967fa.accept_20_3_19_10_1_12337 83 119
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 210 (accept_3_4 82 119
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3
  81 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 80 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 210 (accept_3_4 79 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 119 210 7 11 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 119 210 (accept_3_4 76 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 119 210 (Polychromatic418967fa.accept_16_11_7_2_1_4185 75 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 210 (Polychromatic418967fa.accept_24_2_23_18_1_3594 74 119
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 210 (accept_3_4 73 119
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 210
  (Polychromatic418967fa.accept_19_15_5_1_1_5360 72 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 119 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 71 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 119 210 7 10 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 69
  119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 68 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 210 (accept_3_4 67 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 210 (Polychromatic418967fa.accept_19_9_5_1_1_2766 66 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 210 (accept_3_4 64 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 63 119 210 7 9 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 119 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 119 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 210 (accept_3_4 61 119 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 210 (Polychromatic418967fa.accept_9_6_2_3_1_771
  60 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 210 (accept_3_4 58 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 119 210 7 8 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 119 210 (accept_3_4 55 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 119 210 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 119 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 210 (accept_3_4 52 119 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 210 (Polychromatic418967fa.accept_9_6_2_3_1_771
  51 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 119 210 7 7 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 119 210 (Polychromatic418967fa.accept_25_23_19_10_1_12420 48 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 210 (Polychromatic418967fa.accept_19_9_5_1_1_2766
  47 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 210 (accept_3_4 46
  119 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 119 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 210 (accept_3_4 43 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 119 210 7 6 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 210 (accept_3_4 40 119 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 210 (Polychromatic418967fa.accept_22_17_9_12_1_12419 39
  119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 210
  (Polychromatic418967fa.accept_23_15_4_3_1_12418 38 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 119 210 (accept_3_4 37 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 119 210 (Polychromatic418967fa.accept_20_16_19_10_1_12352 36 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 119 210 7 5 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 119 210 (accept_3_4 34 119 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 210 (accept_3_4 31 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 210 (Polychromatic418967fa.accept_23_7_4_3_1_12417 30 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 119 210 7 4 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 119 210
  (Polychromatic418967fa.accept_16_11_7_2_1_4185 27 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 119 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 210 (accept_3_4 25 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 119 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 210 (Polychromatic418967fa.accept_9_5_2_3_1_194
  23 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 210 (accept_3_4 22
  119 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 119 210 7 3 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 119 210
  (Polychromatic418967fa.accept_22_20_9_12_1_12416 20 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 119 210 (accept_3_4 19 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 119 210 (Polychromatic418967fa.accept_19_18_5_1_1_8255 18 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 210 (accept_3_4 16 119 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 210 (Polychromatic418967fa.accept_9_6_2_3_1_771
  15 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 119 210 7 2 17 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 119 210
  (accept_3_4 13 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 210
  (Polychromatic418967fa.accept_16_12_7_2_1_4159 12 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 119 210 (Polychromatic418967fa.accept_16_11_7_2_1_4185 11 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 210 (accept_3_4 10 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 8
  119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 119 210 7 1 17 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 119 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 6 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 119 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 210 (accept_3_4 4 119 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 119 210 (Polychromatic418967fa.accept_19_3_5_1_1_6811 3 119 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 210
  (Polychromatic418967fa.accept_24_2_23_18_1_3594 2 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 210 (accept_3_4 1 119 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 118 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 118 210 2 46 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 210 (Polychromatic418967fa.accept_16_11_6_2_1_4155 91 118
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 118 210 2 45 59 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 118 210 (accept_3_5 89
  118 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 118 210 2 44 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 118 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 87 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 118 210 2 43 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 118 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 85 118 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 118 210 2 42 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 118 210 (accept_3_5 83 118 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 118 210 2 41 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 118 210 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  81 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 210 2 40 59 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 79 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 118 210 2 39 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 118 210 (accept_3_5 77 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 210 2 38 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 75 118 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 210 2 37 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 210
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 73 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 210 2 36 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 210 (accept_3_5 71 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 210 2 35 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 118 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 210 2 34 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 67 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 210 2 33 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 210 (accept_3_5 65 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 210 2 32 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 118 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 210 2 31 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 61 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 210 2 30 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 210 (accept_3_5 59 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 210 2 29 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 118 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 210 2 28 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 210
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 55 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 210 2 27 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 210 (accept_3_5 53 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 210 2 26 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 118 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 210 2 25 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 210 2 24 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 210 (accept_3_5 47 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 210 2 23 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 118 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 210 2 22 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 210 2 21 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 210 (accept_3_5 41 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 210 2 20 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 118 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 210 2 19 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 210
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 210 2 18 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 210 (accept_3_5 35 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 210 2 17 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 118 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 210 2 16 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 210 2 15 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 210 (accept_3_5 29 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 210 2 14 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 118 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 210 2 13 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 210 2 12 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 210 (accept_3_5 23 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 210 2 11 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 118 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 210 2 10 59 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 210
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 210 2 9 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 118 210 (accept_3_5 17 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 210 2 8 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 118 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 210 2 7 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 210 2 6 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 210 (accept_3_5 11 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 210 2 5 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 118 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 210 2 4 59 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 210 2 3 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 210 (accept_3_5 5 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  210 2 2 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 118 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 210 2 1 59 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 210 (Polychromatic418967fa.accept_16_1_6_2_1_3100 1 118 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 117
  210 (Eq.refl Bool.true) (allA_succ_of_gcd 93 117 210 3 31 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 117 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 92 117 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 117 210 3 30 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 117 210 (Polychromatic418967fa.accept_18_17_9_12_1_2160 89 117 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 88 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 117 210 3 29 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 117 210 (Polychromatic418967fa.accept_12_2_9_6_1_439 86 117 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 210
  (Polychromatic418967fa.accept_20_5_17_10_1_3632 85 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 117 210 3 28 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 117 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 82 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 117 210 3 27 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 117 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 80 117 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 210 3 26 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 210
  (Polychromatic418967fa.accept_16_13_5_2_1_2131 77 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 76 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 117 210 3 25 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 117 210 (Polychromatic418967fa.accept_12_2_9_6_1_439
  74 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 210
  (Polychromatic418967fa.accept_19_16_3_1_1_5389 73 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 117 210 3 24 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 117 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 117 210 3 23 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 117 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 117 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 117 210 3 22 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 117 210
  (Polychromatic418967fa.accept_17_14_15_6_1_4819 65 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 117 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 64 117 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 117 210 3 21 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 117 210
  (Polychromatic418967fa.accept_12_2_9_6_1_439 62 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 210 (Polychromatic418967fa.accept_11_6_7_1_1_564 61 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 117 210 3 20 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 117 210 3 19 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 117 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 117 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 117 210 3 18 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 117 210
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 53 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 117 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 117 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 210 3 17 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 210
  (Polychromatic418967fa.accept_11_6_7_1_1_564 50 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 210 (Polychromatic418967fa.accept_19_11_3_1_1_2799 49 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 210 3 16 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 210 3 15 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 117 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 117 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 210 3 14 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 210
  (Polychromatic418967fa.accept_18_5_9_12_1_8461 41 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 210 3 13 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 210 (Polychromatic418967fa.accept_12_2_9_6_1_439
  38 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 210
  (Polychromatic418967fa.accept_22_15_7_12_1_12415 37 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 117 210 3 12 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 117 210 3 11 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 117 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 117 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 210 3 10 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 210
  (Polychromatic418967fa.accept_16_13_5_2_1_2131 29 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 210 (Polychromatic418967fa.accept_11_6_7_1_1_564 28 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 210 3 9 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 210 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 210
  (Polychromatic418967fa.accept_17_8_15_6_1_4889 25 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 117 210 3 8 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 210 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 117
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 210 3 7 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 210
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 210 3 6 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 210 (Polychromatic418967fa.accept_11_6_7_1_1_564
  17 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 117 210 3 5 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 117 210 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 210 (Polychromatic418967fa.accept_16_13_5_2_1_2131 13 117
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 210 3 4 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 210 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 210 3 3 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 210 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 117 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 210 3 2 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 210 (Polychromatic418967fa.accept_18_5_9_12_1_8461 5 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 117 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 210 3 1 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 210
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 117 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 210 (Polychromatic418967fa.accept_20_1_17_10_1_3563 1 117 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 116
  210 (Eq.refl Bool.true) (allA_succ_of_gcd 94 116 210 2 47 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 210 (Polychromatic418967fa.accept_11_5_6_1_1_988 93 116 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 116 210 2 46 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 116 210 (accept_3_4 91
  116 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 116 210 2 45 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 116 210
  (Polychromatic418967fa.accept_19_13_2_1_1_4054 89 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 116 210 2 44 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 116 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 116 210 2 43 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 116 210 (accept_3_4 85 116 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 116 210 2 42 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 116 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 83
  116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 210 2 41 58 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 81 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 210 2 40 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 210 (accept_3_4 79 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 210 2 39 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 210 2 38 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 75 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 210 2 37 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 210 (accept_3_4 73 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 210 2 36 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 210 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 210 2 35 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 69 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 210 2 34 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 210 (accept_3_4 67 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 210 2 33 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 210 2 32 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 116 210 2 31 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 116 210 (accept_3_4 61 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 210 2 30 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 210 2 29 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 210 2 28 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 210 (accept_3_4 55 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 210 2 27 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 210 (Polychromatic418967fa.accept_13_1_12_2_1_384 53 116 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 210 2 26 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 210 2 25 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 210 (accept_3_4 49 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 210 2 24 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 210 2 23 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 210 2 22 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 210 (accept_3_4 43 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 210 2 21 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 210 2 20 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 210 2 19 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 210 (accept_3_4 37 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 210 2 18 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 210 (Polychromatic418967fa.accept_20_15_16_10_1_6480 35 116 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 210 2 17 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 210 2 16 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 210 (accept_3_4 31 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 210 2 15 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 210 2 14 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 210
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 210 2 13 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 210 (accept_3_4 25 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 210 2 12 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 210 2 11 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 210 2 10 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 210 (accept_3_4 19 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 210 2 9 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 116 210 (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 116 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 210 2 8 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 210 2 7 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 116 210 (accept_3_4 13 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 116 210 2 6 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 116 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 116 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 210 2 5 58 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 210 2 4 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 210 (accept_3_4 7 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  210 2 3 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 116 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 210 2 2 58 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 116 210 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 116 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 210 2 1 58 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 210 (accept_3_4 1 116 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 115
  210 (Eq.refl Bool.true) (allA_succ_of_gcd 95 115 210 5 19 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 115 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 94 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 115 210 (accept_3_5 92 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 115 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 91 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 115 210 5 18 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 115 210 (accept_3_5 89 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 115 210 (Polychromatic418967fa.accept_13_10_11_2_1_3862 88 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 210 (Polychromatic418967fa.accept_9_6_7_3_1_436
  87 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 210 (accept_3_5 86
  115 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 115 210 5 17 23 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 115 210
  (Polychromatic418967fa.accept_20_4_15_10_1_6519 84 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 115 210 (accept_3_5 83 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 115 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 82 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 115 210 5 16 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 115 210
  (Polychromatic418967fa.accept_16_15_3_2_1_4170 79 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 115 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 78 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 210 (accept_3_5 77 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 115 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 115 210 5 15 23 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 115 210 (accept_3_5 74 115 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 210
  (Polychromatic418967fa.accept_11_6_5_1_1_586 72 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 210 (accept_3_5 71 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  115 210 5 14 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 210 (accept_3_5 68 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 115 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 210
  (Polychromatic418967fa.accept_20_6_15_10_1_3555 66 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 115 210 5 13 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 115 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 115 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 210
  (Polychromatic418967fa.accept_16_15_3_2_1_4170 63 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 210 (accept_3_5 62 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 115 210 5 12 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 115 210 (accept_3_5 59 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 115 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 210 (accept_3_5 56 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 115 210 5 11 23 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 115 210
  (Polychromatic418967fa.accept_16_6_3_2_1_3096 54 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 210 (accept_3_5 53 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 210 (Polychromatic418967fa.accept_20_12_15_10_1_6520 52 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 115 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 115 210 5 10 23 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 115 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 115 210 (Polychromatic418967fa.accept_13_9_11_2_1_1491 48 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 210 (accept_3_5 47 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 115 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 115 210 5 9 23 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 115 210 (accept_3_5 44 115 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 210 (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 115
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 210
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 210 (accept_3_5 41 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  115 210 5 8 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 115 210 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 115 210 (accept_3_5 38 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 210 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 115
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 115 210 5 7 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 115 210
  (Polychromatic418967fa.accept_20_14_15_10_1_3554 34 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 210 (accept_3_5 32 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 115 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 115 210 5 6 23 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 115 210 (accept_3_5 29 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 28
  115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 210
  (Polychromatic418967fa.accept_20_7_15_10_1_3628 27 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 115 210 (accept_3_5 26 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 115 210 5 5 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 115 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 210 (accept_3_5 23 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 115 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 210 5 4 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 210 (Polychromatic418967fa.accept_20_18_15_10_1_12414 18 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 210 (accept_3_5 17 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 210 (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 210 5 3 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 210 (accept_3_5 14
  115 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 115 210 (Polychromatic418967fa.accept_20_12_15_10_1_6520 12 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 210 (accept_3_5 11 115 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 115 210 5 2 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 210 (accept_3_5 8 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 210 (Polychromatic418967fa.accept_17_7_13_6_1_811
  7 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 210
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 115 210 5 1 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 115 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 115 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 210 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 115
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 210 (accept_3_5 2 115 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  115 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 114
  210 (Eq.refl Bool.true) (allA_succ_of_gcd 96 114 210 6 16 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 95 114 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 210 2 47 57 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 114 210 3 31 38 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 114 210 2 46 57
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 91 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 210 6 15 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 89 114 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 210 2 44 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 114 210 3 29 38 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 114 210 2 43 57 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 85 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 210 6 14 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 83 114 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 210 2 41 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 114 210 3 27 38 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 114 210 2 40 57 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 79 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 210 6 13 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 114 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 210 2 38 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 114 210 3 25 38 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 114 210 2 37 57 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 73 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 210 6 12 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 71 114 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 210 2 35 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 114 210 3 23 38 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 114 210 2 34 57 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 210 6 11 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 65 114 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 210 2 32 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 114 210 3 21 38 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 114 210 2 31 57 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 210 6 10 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 114 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 210 2 29 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 114 210 3 19 38 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 114 210 2 28 57 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 55 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 210 6 9 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 114 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 114 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 210 2 26 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 114 210 3 17 38 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 210 2 25 57 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 210 6 8 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 114 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 114 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 210 2 23 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 210 3 15 38 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 210 2 22 57 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 210 6 7 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 114 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 210 2 20 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 210 3 13 38 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 210 2 19 57 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 210 6 6 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 114 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 114 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 210 2 17 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 210 3 11 38 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 210 2 16 57 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 210 6 5 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 114 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 210 2 14 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 210 3 9 38 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 210 2 13 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 210 6 4 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 114 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 210 2 11 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 210 3 7 38 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 210 2 10 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 210 6 3 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 114 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 210 2 8 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 210 3 5 38 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 210 2 7 57 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 210 6 2 19 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 114 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 210 2 5 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 210 3 3 38 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 210 2 4 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 7
  114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 210 6 1 19 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 210
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 114 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 114 210 2 2 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 114 210 3 1 38 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 114 210 2 1 57 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 114 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 114 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  113 210 (Eq.refl Bool.true) (allA_succ_of_accept 97 113 210 (accept_3_4 97 113 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 113 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 113 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 95
  113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 210 (accept_3_4 94
  113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 210
  (Polychromatic418967fa.accept_19_17_18_1_1_3980 93 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 113 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 92 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 113 210 (accept_3_4 91 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 113 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 89 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 113 210 (accept_3_4 88 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 113 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 113 210 (Polychromatic418967fa.accept_16_6_1_2_1_3129 86 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 113 210 (accept_3_4 85 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 113 210 (Polychromatic418967fa.accept_13_6_9_2_1_838 84 113
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 113 210 (accept_3_4 82 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 113 210 (Polychromatic418967fa.accept_13_3_9_2_1_1486 81 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 113 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 80 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 113 210 (accept_3_4 79 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 113 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 210
  (Polychromatic418967fa.accept_20_17_13_10_1_5059 77 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 113 210 (accept_3_4 76 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 113 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 113 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 74 113 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 210 (accept_3_4 73 113 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 210 (Polychromatic418967fa.accept_13_7_9_2_1_2167
  72 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 113 210 (accept_3_4 70 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 113 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 113 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 68 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 210 (accept_3_4 67 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 210 (Polychromatic418967fa.accept_13_1_9_2_1_1448 66 113
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 65 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 210 (accept_3_4 64 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 62 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 210 (accept_3_4 61 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 210 (accept_3_4 58 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 210 (accept_3_4 55 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 210 (Polychromatic418967fa.accept_16_6_1_2_1_3129 54 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 210 (accept_3_4 52 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 210 (Polychromatic418967fa.accept_13_11_9_2_1_2969 50 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 210 (accept_3_4 49 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 210 (Polychromatic418967fa.accept_25_23_13_10_1_12413 48
  113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 210 (accept_3_4 46 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 210 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 44 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 210 (accept_3_4 43 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 210
  (Polychromatic418967fa.accept_16_9_1_2_1_2126 41 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 210 (accept_3_4 40 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 210 (accept_3_4 37 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 210 (Polychromatic418967fa.accept_19_17_18_1_1_3980 36 113 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 210 (accept_3_4 34 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 210 (Polychromatic418967fa.accept_13_6_9_2_1_838 32 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 210 (accept_3_4 31 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 210 (Polychromatic418967fa.accept_17_13_11_6_1_4837 30 113
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 210 (accept_3_4 28 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 210 (accept_3_4 25 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 210 (accept_3_4 22 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 210 (Polychromatic418967fa.accept_17_4_11_6_1_3730 21 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 210 (accept_3_4 19 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 210 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 210 (accept_3_4 16 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 210 (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 210 (accept_3_4 13 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 210 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 113
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 210 (accept_3_4 10 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 210 (Polychromatic418967fa.accept_16_9_1_2_1_2126 9 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 210 (accept_3_4 7 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 113 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 210
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 210 (accept_3_4 4 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 210 (accept_3_4 1 113 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  112 210 (Eq.refl Bool.true) (allA_succ_of_gcd 98 112 210 14 7 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 112 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 97 112 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 112 210 2 48 56 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 112 210 (accept_3_5 95
  112 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 112 210 2 47 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 112 210
  (Polychromatic418967fa.accept_12_9_4_6_1_460 93 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 112 210 2 46 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 91 112 210 7 13 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 112 210 2 45 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 112 210 (accept_3_5 89 112 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 112 210 2 44 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 112 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 112 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 112 210 2 43 56 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 112 210
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 85 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 112 210 14 6 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 112 210 (accept_3_5 83 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82
  112 210 2 41 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 112 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 81 112 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 112 210 2 40 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 112 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 79
  112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 112 210 2 39 56 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 112 210 7 11 16 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 112 210 2 38 56
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 112 210
  (Polychromatic418967fa.accept_12_3_4_6_1_434 75 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 112 210 2 37 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 112 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 112 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 112 210 2 36 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 112 210 (accept_3_5 71 112 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 112 210 14 5 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 112 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 69
  112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 210 2 34 56 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 210
  (Polychromatic418967fa.accept_17_16_10_6_1_7313 67 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 112 210 2 33 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 112 210 (accept_3_5 65 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 210 2 32 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 112 210 7 9 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 112 210 2 31 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 112 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 112 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 112 210 2 30 56 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 112 210 (accept_3_5 59 112 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 112 210 2 29 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 112 210
  (Polychromatic418967fa.accept_12_9_4_6_1_460 57 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 112 210 14 4 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 112 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 112 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 112 210 2 27 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 112 210 (accept_3_5 53 112 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 112 210 2 26 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 112 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 112 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 210 2 25 56 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 112 210 7 7 16 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 112 210 2 24 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 112 210
  (accept_3_5 47 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 112 210 2 23 56 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 112 210
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 112 210 2 22 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 112 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 112 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 210 14 3 8 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 210 (accept_3_5 41 112 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 210 2 20 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 210 (Polychromatic418967fa.accept_12_3_4_6_1_434
  39 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 210 2 19 56 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 210 2 18 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 112 210 7 5 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 112 210 2 17 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 112 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 112 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 210 2 16 56 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 210
  (Polychromatic418967fa.accept_23_8_20_3_1_12412 31 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 112 210 2 15 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 112 210 (accept_3_5 29 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 210 14 2 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 112 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 112 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 210 2 13 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 25
  112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 112 210 2 12 56 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 112 210 (accept_3_5 23
  112 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 112 210 2 11 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 112 210 7 3 16 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 112 210 2 10 56 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 210 2 9 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 112 210 (accept_3_5 17 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 112 210 2 8 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 112 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 112 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 210 14 1 8 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 210
  (Polychromatic418967fa.accept_20_13_12_10_1_3619 13 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 112 210 2 6 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 112 210 (accept_3_5 11 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 210 2 5 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 112 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 112 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 210 2 4 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 112 210 7 1 16 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 112 210 2 3 56 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 210 (accept_3_5 5 112 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112 210 2 2 56 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 112 210 (Polychromatic418967fa.accept_11_3_2_1_1_994 3
  112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 210 2 1 56 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 112 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 112 210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 100 111 210 (Eq.refl Bool.true) (allA_succ_of_gcd 99 111 210 3 33 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 111 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 98 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 111 210 3 32 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 111 210
  (Polychromatic418967fa.accept_20_15_11_10_1_5071 95 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 111 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 94 111 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 111 210 3 31 37 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 111 210
  (Polychromatic418967fa.accept_12_8_3_6_1_909 92 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 111 210 (Polychromatic418967fa.accept_18_1_3_12_1_467 91 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 111 210 3 30 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 89
  111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 111 210
  (Polychromatic418967fa.accept_12_4_3_6_1_879 88 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 111 210 3 29 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 111 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 86 111 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 85
  111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 111 210 3 28 37 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 111 210
  (Polychromatic418967fa.accept_13_5_7_2_1_852 83 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 82 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 111 210 3 27 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 111 210 (Polychromatic418967fa.accept_12_8_3_6_1_909
  80 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 210
  (Polychromatic418967fa.accept_18_7_3_12_1_3241 79 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 111 210 3 26 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 111 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 210 (Polychromatic418967fa.accept_12_4_3_6_1_879
  76 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 111 210 3 25 37 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 111 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 74 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 111 210 3 24 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 111 210 (Polychromatic418967fa.accept_17_3_9_6_1_3726
  71 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 210
  (Polychromatic418967fa.accept_12_10_3_6_1_882 70 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 111 210 3 23 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 111 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 68 111 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 210
  (Polychromatic418967fa.accept_16_3_15_2_1_6475 67 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 111 210 3 22 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 111 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 210 (Polychromatic418967fa.accept_12_4_3_6_1_879
  64 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 111 210 3 21 37 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 111 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 62 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 111 210 3 20 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 111 210 (Polychromatic418967fa.accept_17_8_9_6_1_7330
  59 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 210
  (Polychromatic418967fa.accept_12_10_3_6_1_882 58 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 111 210 3 19 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 111 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 210 (Polychromatic418967fa.accept_18_1_3_12_1_467
  55 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 111 210 3 18 37 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 111 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 210 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 210 3 17 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 210 (Polychromatic418967fa.accept_12_2_3_6_1_112
  50 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 111 210 3 16 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 111 210 (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 111 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 210
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 210 3 15 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 111 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 210
  (Polychromatic418967fa.accept_18_7_3_12_1_3241 43 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 111 210 3 14 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 210 (Polychromatic418967fa.accept_12_4_3_6_1_879
  40 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 210 3 13 37 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 210 3 12 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 210 (Polychromatic418967fa.accept_13_9_7_2_1_3869
  35 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 210
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 210 3 11 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 111 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 210 (Polychromatic418967fa.accept_13_5_7_2_1_852
  31 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 210 3 10 37 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 210 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 210 3 9 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 210 (Polychromatic418967fa.accept_12_2_3_6_1_112
  26 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 111 210 3 8 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 111 210 (Polychromatic418967fa.accept_19_4_16_1_1_8332 23 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 111
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 210 3 7 37 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 210
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 210 (Polychromatic418967fa.accept_16_3_15_2_1_6475 19 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 210 3 6 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 210
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 111 210 3 5 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 111 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 210 3 4 37 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 210
  (Polychromatic418967fa.accept_22_11_1_12_1_12411 11 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 111 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 111 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 210 3 3 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 210
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 210 (Polychromatic418967fa.accept_18_7_3_12_1_3241 7 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 210 3 2 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 210
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 111 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 210 3 1 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 111 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 110 210 (Eq.refl Bool.true) (allA_succ_of_gcd 100 110 210 10 10 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 210 (Polychromatic418967fa.accept_12_3_2_6_1_138
  99 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 110 210 2 49 55 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 110 210
  (accept_3_4 97 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 110 210 2 48 55 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 110 210 5 19 22 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 110 210 2 47 55
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 93 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 210 2 46 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 210 (accept_3_4 91 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 210 10 9 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 89 110 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 210 2 44 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 87 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 210 2 43 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 110 210 5 17 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 110 210 2 42 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 110 210 (Polychromatic418967fa.accept_17_15_8_6_1_8733 83 110
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 210 2 41 55 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 81 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 210 10 8 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 210 (accept_3_4 79 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 210 2 39 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 77 110 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 210 2 38 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 110 210 5 15 22 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 110 210 2 37 55 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 110 210 (accept_3_4 73
  110 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 110 210 2 36 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 110 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 110 210 10 7 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 110 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 110 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 110 210 2 34 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 110 210 (accept_3_4 67 110 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 110 210 2 33 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 110 210 5 13 22 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 110 210 2 32 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 210 2 31 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 210 (accept_3_4 61 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 210 10 6 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 110 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 210 2 29 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 210 2 28 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 110 210 5 11 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 110 210 2 27 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 110 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 110 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 210 2 26 55 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 210 10 5 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 210 (accept_3_4 49 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 210 2 24 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 210 (Polychromatic418967fa.accept_13_8_6_2_1_865 47 110 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 210 2 23 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 110 210 5 9 22 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 110 210 2 22 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 110 210 (accept_3_4 43 110 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 110 210 2 21 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 110 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 110 210 10 4 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 110 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 110 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 210 2 19 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 210 (accept_3_4 37 110 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 210 2 18 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 110 210 5 7 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 110 210 2 17 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 210 2 16 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 210 (accept_3_4 31 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 210 10 3 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 210 (Polychromatic418967fa.accept_23_6_18_3_1_12410 29 110 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 210 2 14 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 210 2 13 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 110 210 5 5 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 110 210 2 12 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 110 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 110 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 210 2 11 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 210 10 2 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 210 (accept_3_4 19 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 210 2 9 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 110 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 210 2 8 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 110 210 5 3 22 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 110 210 2 7 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 210 (accept_3_4 13 110 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 210 2 6 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 210
  (Polychromatic418967fa.accept_19_11_15_1_1_12391 11 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 110 210 10 1 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 110 210 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 110 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 210 2 4 55 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 210 (accept_3_4 7 110 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110 210 2 3 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 110 210 5 1 22 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 110 210 2 2 55 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 110 210 2 1 55 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 110 210 (accept_3_4 1 110 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 109 210 (Eq.refl Bool.true) (allA_succ_of_accept 101 109 210 (accept_3_5 101 109 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 109 210 (Polychromatic418967fa.accept_13_9_5_2_1_2185 100 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 99 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 210 (accept_3_5 98 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 97 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 96 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 210 (accept_3_5 95 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 94 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 210
  (Polychromatic418967fa.accept_18_3_1_12_1_4419 93 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 109 210 (accept_3_5 92 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 109 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 109 210 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 210 (accept_3_5 89 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 88 109 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 87 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 109 210 (accept_3_5 86 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 109 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 85 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 210 (Polychromatic418967fa.accept_17_16_7_6_1_7343 84 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 210 (accept_3_5 83 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 210 (Polychromatic418967fa.accept_13_4_5_2_1_1436 82 109
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 210
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 81 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 210 (accept_3_5 80 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 210 (accept_3_5 77 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 210 (accept_3_5 74 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 210 (Polychromatic418967fa.accept_20_13_9_10_1_8083 73 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 210 (Polychromatic418967fa.accept_13_7_5_2_1_401 72 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 210 (accept_3_5 71 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 109 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 210 (accept_3_5 68 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 210 (Polychromatic418967fa.accept_19_9_14_1_1_6792 66 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 210 (accept_3_5 65 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 210 (Polychromatic418967fa.accept_11_9_10_1_1_581 64 109
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 210 (accept_3_5 62 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 210 (accept_3_5 59 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 210
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 210 (accept_3_5 56 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 210 (Polychromatic418967fa.accept_23_8_17_3_1_12380 54 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 210 (accept_3_5 53 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 109 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 210 (accept_3_5 50 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 210 (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 210 (accept_3_5 47 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 210 (Polychromatic418967fa.accept_11_2_10_1_1_1017 46 109
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 210
  (Polychromatic418967fa.accept_20_5_9_10_1_12409 45 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 109 210 (accept_3_5 44 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 109 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 109 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 210 (accept_3_5 41 109 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 210 (Polychromatic418967fa.accept_9_4_1_3_1_190
  40 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 210 (accept_3_5 38 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 210 (Polychromatic418967fa.accept_16_5_13_2_1_2138 37 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 210 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 210 (accept_3_5 35 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 109 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 210 (accept_3_5 32 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 210 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 210 (accept_3_5 29 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 210 (Polychromatic418967fa.accept_19_9_14_1_1_6792 28 109
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 210 (accept_3_5 26 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 210 (accept_3_5 23 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 210
  (Polychromatic418967fa.accept_16_5_13_2_1_2138 21 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 210 (accept_3_5 20 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 210 (Polychromatic418967fa.accept_19_18_14_1_1_8323 18 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 210 (accept_3_5 17 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 109 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 210 (accept_3_5 14 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 210 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 210 (accept_3_5 11 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 210 (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 109
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 210
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 210 (accept_3_5 8 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 210 (accept_3_5 5 109 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 109 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 210 (accept_3_5 2 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 210 (Polychromatic418967fa.accept_20_1_9_10_1_6491 1 109 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 108 210 (Eq.refl Bool.true) (allA_succ_of_gcd 102 108 210 6 17 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 108 210
  (Polychromatic418967fa.accept_23_9_16_3_1_12408 101 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 108 210 2 50 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 99 108 210 3 33 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 108 210 2 49 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 210 (Polychromatic418967fa.accept_13_6_4_2_1_1433
  97 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 108 210 6 16 18 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 108 210
  (Polychromatic418967fa.accept_16_15_12_2_1_6502 95 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 94 108 210 2 47 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 93 108 210 3 31 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 108 210 2 46 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 210
  (Polychromatic418967fa.accept_24_19_12_18_1_8911 91 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 108 210 6 15 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 108 210 (Polychromatic418967fa.accept_13_11_4_2_1_2954 89 108 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 210 2 44 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 108 210 3 29 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 108 210 2 43 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 210
  (Polychromatic418967fa.accept_20_5_8_10_1_11026 85 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 108 210 6 14 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 108 210 (Polychromatic418967fa.accept_13_5_4_2_1_846 83 108 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 210 2 41 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 108 210 3 27 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 108 210 2 40 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 210
  (Polychromatic418967fa.accept_16_15_12_2_1_6502 79 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 108 210 6 13 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 108 210 (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 108 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 210 2 38 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 108 210 3 25 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 108 210 2 37 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 210
  (Polychromatic418967fa.accept_16_9_12_2_1_3093 73 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 210 6 12 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 210 (Polychromatic418967fa.accept_13_6_4_2_1_1433 71 108 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 210 2 35 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 108 210 3 23 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 108 210 2 34 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 210
  (Polychromatic418967fa.accept_19_10_13_1_1_8264 67 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 108 210 6 11 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 108 210 (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 108 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 210 2 32 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 108 210 3 21 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 108 210 2 31 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 210
  (Polychromatic418967fa.accept_22_17_20_12_1_10795 61 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 108 210 6 10 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 108 210 (Polychromatic418967fa.accept_19_2_13_1_1_6831 59 108 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 210 2 29 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 210 3 19 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 210 2 28 54 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 210
  (Polychromatic418967fa.accept_16_7_12_2_1_8902 55 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 210 6 9 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 210 (Polychromatic418967fa.accept_22_9_20_12_1_12407 53 108 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 210 2 26 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 210 3 17 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 210 2 25 54 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 210
  (Polychromatic418967fa.accept_16_1_12_2_1_2136 49 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 210 6 8 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 108 210 (Polychromatic418967fa.accept_16_15_12_2_1_6502 47 108 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 210 2 23 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 210 3 15 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 210 2 22 54 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 210
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 43 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 210 6 7 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 108 210 (Polychromatic418967fa.accept_16_9_12_2_1_3093 41 108 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 210 2 20 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 210 3 13 36 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 210 2 19 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 210
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 210 6 6 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 210 (Polychromatic418967fa.accept_19_16_13_1_1_12406 35 108 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 210 2 17 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 210 3 11 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 210 2 16 54 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 210
  (Polychromatic418967fa.accept_13_5_4_2_1_846 31 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 210 6 5 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 210 (Polychromatic418967fa.accept_19_10_13_1_1_8264 29 108 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 210 2 14 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 210 3 9 36 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 210 2 13 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 210
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 210 6 4 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 210 (Polychromatic418967fa.accept_16_7_12_2_1_8902 23 108 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 210 2 11 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 210 3 7 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 210 2 10 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 210
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 210 6 3 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 210 (Polychromatic418967fa.accept_16_1_12_2_1_2136 17 108 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 210 2 8 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 210 3 5 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 210 2 7 54 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 210
  (Polychromatic418967fa.accept_23_13_16_3_1_7296 13 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 108 210 6 2 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 108 210 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 108 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 210 2 5 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 210 3 3 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 210 2 4 54 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 210
  (Polychromatic418967fa.accept_16_7_12_2_1_8902 7 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 210 6 1 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 210 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 108 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 210 2 2 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 108 210 3 1 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 108 210 2 1 54 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 210 (Polychromatic418967fa.accept_16_1_12_2_1_2136
  1 108 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 107 210 (Eq.refl Bool.true) (allA_succ_of_accept 103 107 210 (accept_3_4 103 107 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 107 210 (Polychromatic418967fa.accept_13_11_3_2_1_863 102 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 107 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 107 210 (accept_3_4 100 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 107 210 (Polychromatic418967fa.accept_18_9_17_12_1_462 99 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 107 210 (Polychromatic418967fa.accept_20_18_7_10_1_3596 98 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 210 (accept_3_4 97 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 107 210
  (Polychromatic418967fa.accept_9_5_8_3_1_437 95 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 107 210 (accept_3_4 94 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 107 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 107 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 92 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 107 210 (accept_3_4 91 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 107 210 (Polychromatic418967fa.accept_13_12_3_2_1_1470 90 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 107 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 107 210 (accept_3_4 88 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 107 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 107 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 86 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 210 (accept_3_4 85 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 107 210 (Polychromatic418967fa.accept_19_8_12_1_1_11084 84 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 107 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 83 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 107 210 (accept_3_4 82 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 107 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 107 210 (Polychromatic418967fa.accept_19_4_12_1_1_3991 80 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 210 (accept_3_4 79 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 107 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 107 210 (accept_3_4 76 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 107 210 (Polychromatic418967fa.accept_13_10_3_2_1_4728 75 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 107 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 74 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 210 (accept_3_4 73 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 210 (Polychromatic418967fa.accept_17_4_5_6_1_8717 72 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 210
  (Polychromatic418967fa.accept_16_7_11_2_1_3117 71 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 107 210 (accept_3_4 70 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 107 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 107 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 68 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 210 (accept_3_4 67 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 210 (Polychromatic418967fa.accept_13_1_3_2_1_1429 66 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 210 (accept_3_4 64 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 210 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 210 (Polychromatic418967fa.accept_13_10_3_2_1_4728 62 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 210 (accept_3_4 61 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 210
  (Polychromatic418967fa.accept_9_5_8_3_1_437 59 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 210 (accept_3_4 58 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 56 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 210 (accept_3_4 55 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 210 (Polychromatic418967fa.accept_16_6_11_2_1_6485 54 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 210 (accept_3_4 52 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 50 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 210 (accept_3_4 49 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 210 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 47 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 210 (accept_3_4 46 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 210 (Polychromatic418967fa.accept_13_5_3_2_1_1499 44 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 210 (accept_3_4 43 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 210 (accept_3_4 40 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 210 (Polychromatic418967fa.accept_16_7_11_2_1_3117 39 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 210 (accept_3_4 37 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 210 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 210
  (Polychromatic418967fa.accept_13_9_3_2_1_399 35 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 210 (accept_3_4 34 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 210 (accept_3_4 31 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 210 (Polychromatic418967fa.accept_19_11_12_1_1_11049 30 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 210 (accept_3_4 28 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 210 (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 210 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 210 (accept_3_4 25 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 210
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 210 (accept_3_4 22 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 210 (accept_3_4 19 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 210 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 210 (accept_3_4 16 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 210 (accept_3_4 13 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 210 (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 210 (accept_3_4 10 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 210 (Polychromatic418967fa.accept_19_8_12_1_1_11084 8 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 210 (accept_3_4 7 107 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 107 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 210 (accept_3_4 4 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 210 (Polychromatic418967fa.accept_17_3_5_6_1_4826 3 107 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 210 (accept_3_4 1 107 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 106 210 (Eq.refl Bool.true) (allA_succ_of_gcd 104 106 210 2 52 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 103 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 106 210 2 51 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 106 210 (accept_3_5 101 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 106 210 2 50 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 106 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 99 106 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 106 210 2 49 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 106 210
  (Polychromatic418967fa.accept_27_16_25_21_1_12405 97 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 106 210 2 48 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 106 210 (accept_3_5 95 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 106 210 2 47 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 106 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 93 106 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 106 210 2 46 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 106 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 91 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 106 210 2 45 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 106 210 (accept_3_5 89 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 106 210 2 44 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 106 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 106 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 210 2 43 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 85 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 210 2 42 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 210 (accept_3_5 83 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 210 2 41 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 81 106 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 210 2 40 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 210
  (Polychromatic418967fa.accept_17_11_4_6_1_2631 79 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 210 2 39 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 210 (accept_3_5 77 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 210 2 38 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 75 106 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 210 2 37 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 73 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 210 2 36 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 210 (accept_3_5 71 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 210 2 35 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 106 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 210 2 34 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 67 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 210 2 33 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 210 (accept_3_5 65 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 210 2 32 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 106 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 210 2 31 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 210
  (Polychromatic418967fa.accept_11_6_7_1_1_564 61 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 210 2 30 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 210 (accept_3_5 59 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 210 2 29 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 106 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 210 2 28 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 55 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 210 2 27 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 210 (accept_3_5 53 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 210 2 26 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 106 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 210 2 25 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 210 2 24 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 210 (accept_3_5 47 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 210 2 23 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 106 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 210 2 22 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 210
  (Polychromatic418967fa.accept_24_19_10_18_1_12404 43 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 106 210 2 21 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 106 210 (accept_3_5 41 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 210 2 20 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 210 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 106 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 210 2 19 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 210 2 18 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 210 (accept_3_5 35 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 210 2 17 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 106 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 210 2 16 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 210 2 15 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 210 (accept_3_5 29 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 210 2 14 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 106 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 210 2 13 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 210
  (Polychromatic418967fa.accept_19_6_11_1_1_6815 25 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 210 2 12 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 210 (accept_3_5 23 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 210 2 11 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 106 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 210 2 10 53 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 210 2 9 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 210 (accept_3_5 17 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 210 2 8 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 106 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 210 2 7 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 210 2 6 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 106 210 (accept_3_5 11 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 210 2 5 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 106 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 210 2 4 53 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 210
  (Polychromatic418967fa.accept_22_7_18_12_1_12377 7 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 106 210 2 3 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 106 210 (accept_3_5 5 106 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 106 210 2 2 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 106 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 106 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 210 2 1 53 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 1
  106 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 210 (allA_succ_of_accept 104 105 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 104 105 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 103 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 105 210 3 34 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 105 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 101 105 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 105 210 5 20 21 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 105 210 3 33 35 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 105 210 7 14 15 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 105 210
  (Polychromatic418967fa.accept_9_7_6_3_1_456 97 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 105 210 3 32 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 95 105 210 5 19 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 94 105 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 94 105 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 105 210 3 31 35 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 105 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 92 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 91 105 210 7 13 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 90 105 210 15 6 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 105 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 89 105 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 210 (Polychromatic418967fa.accept_9_7_6_3_1_456
  88 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 105 210 3 29 35 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 105 210
  (Polychromatic418967fa.accept_9_5_6_3_1_40 86 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 105 210 5 17 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 105 210 21 4 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 105 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 105 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 210 (Polychromatic418967fa.accept_9_1_6_3_1_177
  82 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 105 210 3 27 35 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 105 210 5 16 21
  42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 105 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 105 210 3 26 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 105 210 7 11 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 105 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 105 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 105 210 15 5 7 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 105 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 74 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 210 3 24 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 210 35 2 3 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 105 210 3 23 35 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 210
  (Polychromatic418967fa.accept_9_5_6_3_1_40 68 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 105 210 3 22 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 105 210 5 13 21 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 105 210 21 3 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 105 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 105 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 210 15 4 7 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 210 3 19 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 105 210 7 8 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 105 210 5 11 21 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 105 210 3 18 35 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 210 3 17 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 105 210 5 10 21 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 105 210 7 7 15 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 105 210 3 16 35 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 210 15 3 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 105 210 21 2 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 105 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 210 5 8 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 105 210 3 13 35 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 210 3 12 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 105 210 35 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 34
  105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 210 3 11 35 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 210
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 210 15 2 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 105 210 7 4 15 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 105 210 3 9 35 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 105 210 5 5 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 105 210 3 8 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 105 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 105 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 210 21 1 5 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 105 210 5 4 21 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 105 210 3 6 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 105 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 105 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 210 15 1 7 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 105 210 7 2 15 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 105 210 3 4 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 105 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 210 5 2 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 105 210 3 3 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 8
  105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 105 210 7 1 15 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 105 210 3 2 35 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 105 210 5 1 21 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 105 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 210 3 1 35 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 105 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 105 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 210 (allA_succ_of_accept 103 104 210 (accept_3_4 103 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 210 2 51 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 101 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 210 2 50 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 99 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 210 2 49 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 210 (accept_3_4 97 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 210 2 48 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 210 (Polychromatic418967fa.accept_20_15_4_10_1_9538 95 104 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 210 2 47 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 93 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 210 2 46 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 210 (accept_3_4 91 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 210 2 45 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 89 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 210 2 44 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 87 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 210 2 43 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 210 (accept_3_4 85 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 210 2 42 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 83 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 210 2 41 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 81 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 210 2 40 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 210 (accept_3_4 79 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 210 2 39 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 210 (Polychromatic418967fa.accept_28_21_20_14_1_12403 77 104 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 210 2 38 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 75 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 210 2 37 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 210 (accept_3_4 73 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 210 2 36 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 210 2 35 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 69 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 210 2 34 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 210 (accept_3_4 67 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 210 2 33 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 65 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 210 2 32 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 210 2 31 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 210 (accept_3_4 61 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 210 2 30 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 210 (Polychromatic418967fa.accept_19_2_9_1_1_4029 59 104 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 210 2 29 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 210 2 28 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 210 (accept_3_4 55 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 210 2 27 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 210 2 26 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 51 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 210 2 25 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 210 (accept_3_4 49 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 210 2 24 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 210 2 23 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 210 2 22 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 210 (accept_3_4 43 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 210 2 21 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 210 (Polychromatic418967fa.accept_20_1_4_10_1_3645 41 104 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 210 2 20 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 210
  (Polychromatic418967fa.accept_11_6_5_1_1_586 39 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 210 2 19 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 210 (accept_3_4 37 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 210 2 18 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 210 2 17 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 210 2 16 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 210 (accept_3_4 31 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 210 2 15 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 210 2 14 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 210 2 13 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 210 (accept_3_4 25 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 210 2 12 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 210 (Polychromatic418967fa.accept_22_1_16_12_1_7499 23 104 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 210 2 11 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 210 2 10 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 210 (accept_3_4 19 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 210 2 9 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 104 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 210 2 8 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 104 210 2 7 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 104 210 (accept_3_4 13 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 104 210 2 6 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 104 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 104 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 210 2 5 52 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 210 2 4 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 210 (accept_3_4 7 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  210 2 3 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 210 (Polychromatic418967fa.accept_19_5_9_1_1_5393 5 104 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 210 2 2 52 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 104 210 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 104 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 210 2 1 52 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 210 (accept_3_4 1 104 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 210 (allA_succ_of_accept 102 103 210 (Polychromatic418967fa.accept_19_7_8_1_1_4028 102 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 210 (accept_3_5 101 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 103 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 100 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 210
  (Polychromatic418967fa.accept_20_19_3_10_1_3588 99 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 103 210 (accept_3_5 98 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 103 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 96 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 210 (accept_3_5 95 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 210 (Polychromatic418967fa.accept_13_3_12_2_1_385
  94 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 93 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 210 (accept_3_5 92 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 91 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 210 (Polychromatic418967fa.accept_17_5_1_6_1_2615 90 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 210 (accept_3_5 89 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 87 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 210 (accept_3_5 86 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 210 (Polychromatic418967fa.accept_13_6_12_2_1_4707 84 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 210 (accept_3_5 83 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 210 (accept_3_5 80 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 79 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 210 (accept_3_5 77 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 210 (Polychromatic418967fa.accept_16_12_7_2_1_4159 76 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 210
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 75 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 103 210 (accept_3_5 74 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 210 (Polychromatic418967fa.accept_19_15_8_1_1_6794 72 103
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 210 (accept_3_5 71 103
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 70 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 210 (accept_3_5 68 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 103 210 (Polychromatic418967fa.accept_20_7_3_10_1_12341 67 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 210
  (Polychromatic418967fa.accept_13_1_12_2_1_384 66 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 210 (accept_3_5 65 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 210 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 210 (accept_3_5 62 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 210 (accept_3_5 59 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 210 (Polychromatic418967fa.accept_13_6_12_2_1_4707 58 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 210 (accept_3_5 56 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 210
  (Polychromatic418967fa.accept_17_3_1_6_1_251 54 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 210 (accept_3_5 53 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 210 (accept_3_5 50 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 210
  (Polychromatic418967fa.accept_26_22_25_2_1_10570 48 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 103 210 (accept_3_5 47 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 103 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 210 (accept_3_5 44 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 210 (Polychromatic418967fa.accept_9_7_4_3_1_204
  43 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 210 (accept_3_5 41 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 210 (Polychromatic418967fa.accept_13_1_12_2_1_384 40 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 210 (Polychromatic418967fa.accept_17_5_1_6_1_2615 39 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 210 (accept_3_5 38 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 210
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 103 210 (accept_3_5 35 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 103 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 210 (accept_3_5 32 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 210
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 31 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 103 210 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 210 (accept_3_5 29 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 103 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 210 (Polychromatic418967fa.accept_13_1_12_2_1_384
  27 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 210 (accept_3_5 26
  103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 103 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 210 (accept_3_5 23 103 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 103 210 (Polychromatic418967fa.accept_17_5_1_6_1_2615 22 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 210 (accept_3_5 20 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 210 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 210 (accept_3_5 17 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 210
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 210 (accept_3_5 14 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 210 (Polychromatic418967fa.accept_16_12_7_2_1_4159 12 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 210 (accept_3_5 11 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 103 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 210 (accept_3_5 8 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 210 (accept_3_5 5 103 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 210 (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 103 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 210
  (Polychromatic418967fa.accept_13_3_12_2_1_385 3 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 210 (accept_3_5 2 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  210))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 210 (allA_succ_of_accept 101 102 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 101 102 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 102 210 2 50 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 102 210 3 33 34 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 102 210 2 49 51 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 210
  (Polychromatic418967fa.accept_16_1_6_2_1_3100 97 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 210 6 16 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 210 (Polychromatic418967fa.accept_13_4_11_2_1_1458 95 102 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 102 210 2 47 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 102 210 3 31 34 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 102 210 2 46 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 210
  (Polychromatic418967fa.accept_16_11_6_2_1_4155 91 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 210 6 15 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 210 (Polychromatic418967fa.accept_16_9_6_2_1_3101 89 102 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 210 2 44 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 102 210 3 29 34 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 102 210 2 43 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 210
  (Polychromatic418967fa.accept_20_5_2_10_1_3576 85 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 210 6 14 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 210 (Polychromatic418967fa.accept_16_3_6_2_1_4157 83 102 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 210 2 41 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 102 210 3 27 34 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 102 210 2 40 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 210
  (Polychromatic418967fa.accept_11_2_3_1_1_244 79 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 210 6 13 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 210 (Polychromatic418967fa.accept_22_11_14_12_1_7700 77 102 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 210 2 38 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 102 210 3 25 34 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 102 210 2 37 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 210
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 73 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 210 6 12 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 210 (Polychromatic418967fa.accept_24_23_6_18_1_12350 71 102 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 210 2 35 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 102 210 3 23 34 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 102 210 2 34 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 210
  (Polychromatic418967fa.accept_16_3_6_2_1_4157 67 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 210 6 11 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 210 (Polychromatic418967fa.accept_16_1_6_2_1_3100 65 102 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 210 2 32 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 102 210 3 21 34 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 102 210 2 31 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 210
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 61 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 210 6 10 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 210 (Polychromatic418967fa.accept_16_11_6_2_1_4155 59 102 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 210 2 29 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 102 210 3 19 34 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 102 210 2 28 51 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 210
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 210 6 9 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 102 210 (Polychromatic418967fa.accept_20_13_2_10_1_2301 53 102 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 210 2 26 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 210 3 17 34 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 210 2 25 51 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 210
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 102 210 6 8 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 102 210 (Polychromatic418967fa.accept_22_3_14_12_1_7651 47 102 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 210 2 23 51 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 210 3 15 34 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 210 2 22 51
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 210
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 210 6 7 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 102 210 (Polychromatic418967fa.accept_16_9_6_2_1_3101 41 102 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 210 2 20 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 210 3 13 34 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 210 2 19 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 210
  (Polychromatic418967fa.accept_19_18_7_1_1_2770 37 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 210 6 6 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 102 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 102 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 210 2 17 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 210 3 11 34 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 210 2 16 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 210
  (Polychromatic418967fa.accept_19_12_7_1_1_5400 31 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 210 6 5 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 102 210 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 102 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 210 2 14 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 210 3 9 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 210 2 13 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 210
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 25 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 210 6 4 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 210 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 102 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 210 2 11 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 210 3 7 34 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 210 2 10 51 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 210
  (Polychromatic418967fa.accept_16_3_6_2_1_4157 19 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 210 6 3 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 210 (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 102 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 210 2 8 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 210 3 5 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 210 2 7 51 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 210
  (Polychromatic418967fa.accept_11_2_3_1_1_244 13 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 210 6 2 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 102 210 (Polychromatic418967fa.accept_16_11_6_2_1_4155 11 102 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 210 2 5 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 210 3 3 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 210 2 4 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 210 (Polychromatic418967fa.accept_23_7_10_3_1_12402
  7 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 210 6 1 17 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 210
  (Polychromatic418967fa.accept_20_5_2_10_1_3576 5 102 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 102 210 2 2 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 102 210 3 1 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 102 210 2 1 51 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 102 210 (Polychromatic418967fa.accept_16_1_6_2_1_3100 1 102 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 210 (allA_succ_of_accept 100 101 210 (accept_3_4 100 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 101 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 98 101 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 210 (accept_3_4 97 101 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 210 (Polychromatic418967fa.accept_9_6_2_3_1_771
  96 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 210 (accept_3_4 94 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 210 (Polychromatic418967fa.accept_16_13_5_2_1_2131 93 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 210 (Polychromatic418967fa.accept_17_7_16_6_1_3705 92 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 210 (accept_3_4 91 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 210 (Polychromatic418967fa.accept_13_12_10_2_1_1451 90 101
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 89 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 210 (accept_3_4 88 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 86 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 210 (accept_3_4 85 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 210 (Polychromatic418967fa.accept_13_6_10_2_1_1449 84 101 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 210 (accept_3_4 82 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 210 (Polychromatic418967fa.accept_13_3_10_2_1_381 81 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 80 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 210 (accept_3_4 79 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 210 (accept_3_4 76 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 210 (Polychromatic418967fa.accept_20_14_1_10_1_12401 74 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 210 (accept_3_4 73 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 210 (Polychromatic418967fa.accept_25_22_1_10_1_12400 72
  101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 210 (accept_3_4 70 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 68 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 210 (accept_3_4 67 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 210 (Polychromatic418967fa.accept_25_16_1_10_1_12399 66 101 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 210
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 210 (accept_3_4 64 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 210 (accept_3_4 61 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 210 (accept_3_4 58 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 210 (Polychromatic418967fa.accept_13_5_10_2_1_856 57 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 210 (Polychromatic418967fa.accept_19_18_6_1_1_12398 56 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 210 (accept_3_4 55 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 210 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 101
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 210 (accept_3_4 52 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 210 (accept_3_4 49 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 210 (Polychromatic418967fa.accept_19_10_6_1_1_6828 48 101 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 210 (accept_3_4 46 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 210 (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 210 (accept_3_4 43 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 210 (accept_3_4 40 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 210 (Polychromatic418967fa.accept_13_12_10_2_1_1451 38 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 210 (accept_3_4 37 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 210 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 101
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 210 (accept_3_4 34 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 210 (accept_3_4 31 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 210 (Polychromatic418967fa.accept_19_11_6_1_1_2826 30 101 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 210
  (Polychromatic418967fa.accept_13_3_10_2_1_381 29 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 210 (accept_3_4 28 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 210 (accept_3_4 25 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 210 (accept_3_4 22 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 210 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 210 (Polychromatic418967fa.accept_25_20_1_10_1_12397 20 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 210 (accept_3_4 19 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 210 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 101
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 210 (accept_3_4 16 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 210 (accept_3_4 13 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 210 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 101 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 210 (accept_3_4 10 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 210 (Polychromatic418967fa.accept_17_9_16_6_1_4820 9 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 210 (accept_3_4 7 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 101 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 210 (accept_3_4 4 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 210 (Polychromatic418967fa.accept_19_2_6_1_1_9729 2 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 210 (accept_3_4 1 101 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  210)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_210_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


