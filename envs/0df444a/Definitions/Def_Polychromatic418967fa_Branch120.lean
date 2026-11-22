-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch120
-- name    : Polychromatic418967fa_Branch120
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:12:08.329285+00:00
-- url     : https://prove2.me/theorems/e95a4f11-ac0a-4e14-904d-d67e3a397b16
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_120 : allB 120 120 :=
  allB_succ' 2 119 120 (Eq.refl Bool.true) (allA_succ_of_accept 1 119 120 (accept_3_4 1 119 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119 120)) (allB_succ' 3 118 120 (Eq.refl Bool.true) (allA_succ_of_gcd 2 118 120 2 1 59
  60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 120
  (Polychromatic418967fa.accept_25_1_18_20_1_5828 1 118 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 118 120))) (allB_succ' 4 117 120 (Eq.refl Bool.true) (allA_succ_of_gcd 3 117 120 3 1 39 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 120
  (Polychromatic418967fa.accept_19_2_3_6_1_4415 2 117 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 120 (Polychromatic418967fa.accept_19_1_3_6_1_5827 1 117 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 120)))) (allB_succ' 5 116 120 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  116 120 4 1 29 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 116 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 116 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 116 120 2 1 58 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 116 120 (accept_3_4 1 116 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  120))))) (allB_succ' 6 115 120 (Eq.refl Bool.true) (allA_succ_of_gcd 5 115 120 5 1 23 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 115 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 115 120 (Polychromatic418967fa.accept_18_3_7_12_1_1196 3 115 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 120 (accept_3_5 2 115 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 115 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 115 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 120)))))) (allB_succ' 7 114 120 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 114 120 6 1 19 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 114 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 120 2 2 57 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 120 3 1 38 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 120 2 1 57 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 114 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 120))))))) (allB_succ' 8 113 120 (Eq.refl
  Bool.true) (allA_succ_of_accept 7 113 120 (accept_3_4 7 113 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 113 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 113 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 120 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 113 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 120 (accept_3_4 4 113 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 120 (Polychromatic418967fa.accept_19_3_18_6_1_3112
  3 113 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 113 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 120 (accept_3_4 1 113 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  120)))))))) (allB_succ' 9 112 120 (Eq.refl Bool.true) (allA_succ_of_gcd 8 112 120 8 1 14 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 120
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 112 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 112 120 2 3 56 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 120 (accept_3_5 5 112 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  120 4 1 28 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 120 (Polychromatic418967fa.accept_19_3_17_6_1_1991 3 112 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 120 2 1 56 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 112 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 112 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 120))))))))) (allB_succ' 10 111 120 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 111 120 3 3 37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 120 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 111 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 120 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 111
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 120 3 2 37 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 111 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 120 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 111 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 120 3 1 37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 111 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 120
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 111 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 120)))))))))) (allB_succ' 11 110 120 (Eq.refl Bool.true) (allA_succ_of_gcd 10 110 120 10 1 11 12
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 120
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 110 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 120 2 4 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 120 (accept_3_4 7 110 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  120 2 3 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 110
  120 5 1 22 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 110
  120 2 2 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  110 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 110 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 110 120 2 1 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 110 120 (accept_3_4 1 110 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  120))))))))))) (allB_succ' 12 109 120 (Eq.refl Bool.true) (allA_succ_of_accept 11 109 120 (accept_3_5 11 109 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 10
  109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 120
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 120 (accept_3_5 8 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 109 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 120 (accept_3_5 5 109 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 109 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 120 (accept_3_5 2 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 120 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 109 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 120)))))))))))) (allB_succ' 13 108 120 (Eq.refl Bool.true) (allA_succ_of_gcd 12 108 120 12 1
  9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 120 2 5 54 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 108 120 3 3 36 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 108 120 4 2 27 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 120 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 108 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 120 6 1 18 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 120 4 1 27 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 108 120 3 1 36 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 108 120 2 1 54 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 120
  (Polychromatic418967fa.accept_11_1_9_10_1_184 1 108 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 120))))))))))))) (allB_succ' 14 107 120 (Eq.refl Bool.true) (allA_succ_of_accept 13 107 120 (accept_3_4
  13 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 120
  (Polychromatic418967fa.accept_16_12_11_8_1_832 12 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 107 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 107 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 120 (accept_3_4 10 107 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 107 120 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 107 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 120 (Polychromatic418967fa.accept_19_8_12_6_1_1976
  8 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 120 (accept_3_4 7
  107 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 107 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 107 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 120 (accept_3_4 4 107 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 107 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 107 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  107 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 120 (accept_3_4 1 107
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107 120)))))))))))))) (allB_succ' 15 106 120 (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 106 120 2 7 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 106 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 106 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 120 2 6 53 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 120 (accept_3_5 11 106 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 120 2 5 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 120 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9
  106 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 120 2 4 53 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 120
  (Polychromatic418967fa.accept_21_7_1_15_1_680 7 106 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 120 2 3 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 120 (accept_3_5 5 106 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  120 2 2 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 120 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 106 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 120 2 1 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 106 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 106 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 120))))))))))))))) (allB_succ' 16 105 120 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 105 120 15 1 7 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 105 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 105 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 120 3 4 35 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 105 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 105 120 5 2 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 105 120 3 3 35 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 105 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 105 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 105 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 120 3 2 35 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 105 120 5 1 21 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 120
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 105 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 120 3 1 35 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 105 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 105 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 120)))))))))))))))) (allB_succ' 17 104 120
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 104 120 8 2 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 104 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 104 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 120 2 7 52 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 120 (accept_3_4 13 104 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 120 4 3 26 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 104 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 120 2 5 52 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 104 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 120 8 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 120 (accept_3_4 7 104 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 120 2 3 52 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 104 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 120 4 1 26 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 120 (Polychromatic418967fa.accept_17_3_2_1_1_1367 3
  104 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 120 2 1 52 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 120 (accept_3_4 1
  104 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104 120))))))))))))))))) (allB_succ' 18 103 120 (Eq.refl
  Bool.true) (allA_succ_of_accept 17 103 120 (accept_3_5 17 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 103 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 103 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 103 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 120 (accept_3_5 14 103 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 120 (Polychromatic418967fa.accept_7_6_5_1_1_416
  13 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 120
  (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 120 (accept_3_5 11 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 120 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 103 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 120 (accept_3_5 8 103 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 103 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 120
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 120 (accept_3_5 5 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 103 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 103 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 120 (accept_3_5 2 103 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 103 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 120)))))))))))))))))) (allB_succ' 19 102 120
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 102 120 6 3 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 102 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 102 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 120 2 8 51 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 120 3 5 34 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 120 2 7 51 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 120
  (Polychromatic418967fa.accept_19_13_7_6_1_5826 13 102 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 120 6 2 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 102 120 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 102 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 120 2 5 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 120 3 3 34 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 120 2 4 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 120 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  7 102 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 120 6 1 17 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 102 120 2 2 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 102 120 3 1 34 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 102 120 2 1 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 102 120 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 102 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102 120))))))))))))))))))) (allB_succ' 20 101 120 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 101 120 (accept_3_4 19 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 101 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 120 (accept_3_4 16 101 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 101 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 120 (accept_3_4 13 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 101 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 120 (accept_3_4 10 101 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 101 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 120
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 120 (accept_3_4 7 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 120 (accept_3_4 4 101 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 120 (Polychromatic418967fa.accept_16_3_5_8_1_4543 3 101 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 120 (accept_3_4 1 101 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  120)))))))))))))))))))) (allB_succ' 21 100 120 (Eq.refl Bool.true) (allA_succ_of_gcd 20 100 120 20 1 5 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 120
  (Polychromatic418967fa.accept_13_6_9_3_1_915 19 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 120 2 9 50 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 100 120 (accept_3_5 17 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  100 120 4 4 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15
  100 120 5 3 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14
  100 120 2 7 50 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  13 100 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 100 120 4 3 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 100 120 (accept_3_5 11 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 100 120 10 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 100 120 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 100 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 120 4 2 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7
  100 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 120 2 3 50 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 100 120 5 1 20 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 100 120 4 1 25 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 100 120
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 100 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 100 120 2 1 50 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 100 120 (Polychromatic418967fa.accept_14_1_2_8_1_655 1 100 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 100 120))))))))))))))))))))) (allB_succ' 22 99 120 (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 99 120 3 7 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 99 120 (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 99 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 120 (Polychromatic418967fa.accept_22_19_11_10_1_5825 19 99
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 120 3 6 33 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 120
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 99 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 120 (Polychromatic418967fa.accept_14_2_1_8_1_650 16 99 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 120 3 5 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 120 (Polychromatic418967fa.accept_22_14_11_10_1_5824 14 99
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 120
  (Polychromatic418967fa.accept_16_13_3_8_1_2422 13 99 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 99 120 3 4 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 99 120 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 99 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 120 (Polychromatic418967fa.accept_17_10_14_1_1_5823 10 99
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 120 3 3 33 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 120
  (Polychromatic418967fa.accept_22_8_11_10_1_5822 8 99 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 120 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 99 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 120 3 2 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 120 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 99 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 120
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 4 99 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 99 120 3 1 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 99 120 (Polychromatic418967fa.accept_14_2_1_8_1_650 2 99 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 120 (Polychromatic418967fa.accept_22_1_11_10_1_5808 1 99 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 120)))))))))))))))))))))) (allB_succ' 23 98
  120 (Eq.refl Bool.true) (allA_succ_of_gcd 22 98 120 2 11 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 120 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 98 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 120 2 10 49 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 120 (accept_3_4 19
  98 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 120 2 9 49 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 120
  (Polychromatic418967fa.accept_13_4_7_3_1_92 17 98 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 98 120 2 8 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 98 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 98 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 120 2 7 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 120 (accept_3_4 13 98 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 98 120 2 6 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 98 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 98 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 120 2 5 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 120 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9
  98 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 120 2 4 49 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 120 (accept_3_4 7 98
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 120 2 3 49 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98 120
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 98 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 98 120 2 2 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 98 120 (Polychromatic418967fa.accept_18_3_8_12_1_3283 3 98 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 120 2 1 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 120 (accept_3_4 1 98 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 120))))))))))))))))))))))) (allB_succ' 24 97 120 (Eq.refl Bool.true) (allA_succ_of_accept 23
  97 120 (accept_3_5 23 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 120
  (Polychromatic418967fa.accept_9_4_7_3_1_43 22 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 97 120 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 97 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 120 (accept_3_5 20 97 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 97 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 97 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 120 (Polychromatic418967fa.accept_13_5_6_3_1_868
  18 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 120 (accept_3_5 17
  97 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 97 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 97 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 120 (accept_3_5 14 97 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 97 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 97 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 12
  97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 120 (accept_3_5 11 97
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 120 (Polychromatic418967fa.accept_9_1_7_3_1_41
  10 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 120 (accept_3_5 8 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  120 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 97 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 120 (accept_3_5 5 97 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 97 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 120
  (Polychromatic418967fa.accept_18_3_7_12_1_1196 3 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 120 (accept_3_5 2 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 97 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 120)))))))))))))))))))))))) (allB_succ' 25 96 120 (Eq.refl Bool.true) (allA_succ_of_gcd 24 96 120 24 1 4
  5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 96 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 96 120 2 11 48 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 96 120 3 7 32 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 96 120 4 5 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 96 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 120 6 3 16 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 96 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 120 8 2 12 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 96 120 3 5 32 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 96 120 2 7 48 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 120
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 96 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 120 12 1 8 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 96 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 120 2 5 48 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 96 120 3 3 32 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 96 120 8 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 96 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 120 6 1 16 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 96 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 120 4 1 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 96 120 3 1 32 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 96 120 2 1 48 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 96 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96 120))))))))))))))))))))))))) (allB_succ' 26 95 120 (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 95 120 5 5 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 95 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 120 (Polychromatic418967fa.accept_16_7_15_8_1_278 23 95 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 120 (accept_3_4 22 95 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 120
  (Polychromatic418967fa.accept_22_21_7_10_1_5821 21 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 95 120 5 4 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 95 120 (accept_3_4 19 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 120 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 95 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 120 (accept_3_4 16 95 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 95 120 5 3 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 95 120 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 95 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 120 (accept_3_4 13 95 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 95 120 5 2 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 95 120 (Polychromatic418967fa.accept_16_9_15_8_1_3425 9 95 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 120 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 95 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 120 (accept_3_4 7 95 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 6
  95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 120 5 1 19 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 120 (accept_3_4 4 95
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 120 (Polychromatic418967fa.accept_7_3_4_1_1_71
  3 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 120 (accept_3_4 1 95 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  120)))))))))))))))))))))))))) (allB_succ' 27 94 120 (Eq.refl Bool.true) (allA_succ_of_gcd 26 94 120 2 13 47 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 120 2 12 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 94 120 (accept_3_5 23 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94
  120 2 11 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  94 120 (Polychromatic418967fa.accept_22_21_6_10_1_4188 21 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 94 120 2 10 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 94 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 94 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 120 2 9 47 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 120 (accept_3_5 17 94 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94 120 2 8 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 94 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 94 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 120 2 7 47 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 120
  (Polychromatic418967fa.accept_32_13_30_24_1_5820 13 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 94 120 2 6 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 94 120 (accept_3_5 11 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 94 120 2 5 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 94 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 94 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 120 2 4 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 94 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 120 2 3 47 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 120 (accept_3_5 5 94 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 120 2 2 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94 120 (Polychromatic418967fa.accept_17_3_9_1_1_1344 3
  94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 120 2 1 47 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 120
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 94 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 120))))))))))))))))))))))))))) (allB_succ' 28 93 120 (Eq.refl Bool.true) (allA_succ_of_gcd 27 93 120 3 9
  31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 120
  (Polychromatic418967fa.accept_11_4_5_10_1_926 26 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 120 (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 93 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 120 3 8 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 120 (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 93 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 120
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 22 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 120 3 7 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 93 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 120 (Polychromatic418967fa.accept_16_3_13_8_1_1594 19 93
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 120 3 6 31 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 120
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 120 (Polychromatic418967fa.accept_21_16_9_15_1_4265 16 93 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 120 3 5 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 120 (Polychromatic418967fa.accept_13_1_2_3_1_911 14 93 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 120 3 4 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 120 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 93 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 93 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 120 3 3 31 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 120
  (Polychromatic418967fa.accept_18_8_3_12_1_3247 8 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 120 (Polychromatic418967fa.accept_17_7_8_1_1_1373 7 93 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 120 3 2 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 120 (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 93 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 120
  (Polychromatic418967fa.accept_11_4_5_10_1_926 4 93 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 120 3 1 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 120 (Polychromatic418967fa.accept_18_2_3_12_1_1155 2 93 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 120 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 93 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 120)))))))))))))))))))))))))))) (allB_succ'
  29 92 120 (Eq.refl Bool.true) (allA_succ_of_gcd 28 92 120 4 7 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 120 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 92 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 120 2 13 46 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 120 (accept_3_4 25
  92 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 120 4 6 23 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 92 120 2 11 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 92 120 (Polychromatic418967fa.accept_16_5_12_8_1_2521 21 92 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 120 4 5 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 120 (accept_3_4 19 92 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 92 120 2 9 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 92 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 92 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 120 4 4 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 15
  92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 120 2 7 46 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 120 (accept_3_4 13
  92 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 120 4 3 23 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 120
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 92 120 2 5 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 92 120 (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 92 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 120 4 2 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 120 (accept_3_4 7 92 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 92 120 2 3 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 92 120 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 92 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 120 4 1 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 120 (Polychromatic418967fa.accept_16_3_12_8_1_808 3
  92 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 120 2 1 46 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 120 (accept_3_4 1 92
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 120))))))))))))))))))))))))))))) (allB_succ' 30 91 120
  (Eq.refl Bool.true) (allA_succ_of_accept 29 91 120 (accept_3_5 29 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 91 120 (Polychromatic418967fa.accept_16_12_11_8_1_832 28 91 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 120 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 91 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 120 (accept_3_5 26 91 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 25
  91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 120
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 120 (accept_3_5 23 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 120 (Polychromatic418967fa.accept_16_5_11_8_1_3431 21 91 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 120 (accept_3_5 20 91 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 120 (Polychromatic418967fa.accept_16_3_11_8_1_830 19 91 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 120
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 120 (accept_3_5 17 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 91 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 120 (accept_3_5 14 91 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 91 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 120
  (Polychromatic418967fa.accept_16_12_11_8_1_832 12 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 120 (accept_3_5 11 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 120 (Polychromatic418967fa.accept_19_10_15_6_1_5772 10 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 120 (Polychromatic418967fa.accept_19_9_15_6_1_4396 9 91 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 120 (accept_3_5 8 91 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 91 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 120
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 120 (accept_3_5 5 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  120 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 91 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 120 (Polychromatic418967fa.accept_16_3_11_8_1_830 3 91 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 120 (accept_3_5 2 91 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 120 (Polychromatic418967fa.accept_14_1_7_8_1_2063 1 91 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 120)))))))))))))))))))))))))))))) (allB_succ' 31 90 120 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 90 120 30 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 120 (Polychromatic418967fa.accept_19_10_14_6_1_5819 29 90 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 120 2 14 45 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 90 120 3 9 30 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 90 120 2 13 45 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 120 5 5 18 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 120 6 4 15 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 90 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 120 2 11 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 90 120 3 7 30 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 90 120 10 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 90 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 120 6 3 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 120 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 90 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 120 2 8 45 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 120 15 1 6 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 120 2 7 45 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 120
  (Polychromatic418967fa.accept_21_13_6_15_1_5818 13 90 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 120 6 2 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 120 (Polychromatic418967fa.accept_19_11_14_6_1_4378 11 90 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 120 10 1 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 120 3 3 30 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 90 120 2 4 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 120 (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 90 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 120 6 1 15 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 120 5 1 18 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 120 2 2 45 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 90 120 3 1 30 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 120 2 1 45 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 120
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 90 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 120))))))))))))))))))))))))))))))) (allB_succ' 32 89 120 (Eq.refl Bool.true) (allA_succ_of_accept 31 89
  120 (accept_3_4 31 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 120
  (Polychromatic418967fa.accept_19_11_13_6_1_5817 30 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 89 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 120 (accept_3_4 28 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 89 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 89 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 120 (Polychromatic418967fa.accept_19_7_13_6_1_1914
  26 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 120 (accept_3_4 25
  89 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 89 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 120 (accept_3_4 22 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 89 120 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 89 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 120
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 120 (accept_3_4 19 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 120 (accept_3_4 16 89 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 89 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 120
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 120 (accept_3_4 13 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 120 (Polychromatic418967fa.accept_16_12_9_8_1_2508 12 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 89 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 120 (accept_3_4 10 89 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 120 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 89 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 120
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 120 (accept_3_4 7 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  120 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 120 (accept_3_4 4 89 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 89 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  89 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 120 (accept_3_4 1 89 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 120)))))))))))))))))))))))))))))))) (allB_succ' 33 88 120
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 88 120 8 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 88 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 88 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 120 2 15 44 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 120 (accept_3_5 29 88 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 120 4 7 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 120 (Polychromatic418967fa.accept_18_9_16_12_1_1143
  27 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 120 2 13 44 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 120
  (Polychromatic418967fa.accept_14_11_4_8_1_664 25 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 120 8 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 120 (accept_3_5 23 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  120 2 11 44 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  88 120 (Polychromatic418967fa.accept_19_2_12_6_1_5816 21 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 120 4 5 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 88 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 88 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 120 2 9 44 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 120 (accept_3_5 17 88 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 120 8 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 88 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 88 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 120 2 7 44 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 120
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 120 4 3 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 120 (accept_3_5 11 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  120 2 5 44 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 120 (Polychromatic418967fa.accept_17_9_3_1_1_2275 9 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 120 8 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 120 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 88 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 120 2 3 44 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 120 (accept_3_5 5 88 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 120 4 1 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 88 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 120 2 1 44 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 120
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 88 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 120))))))))))))))))))))))))))))))))) (allB_succ' 34 87 120 (Eq.refl Bool.true) (allA_succ_of_gcd 33 87
  120 3 11 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  87 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 87 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 87 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 120 3 10 29 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 120 3 9 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 87 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 120 3 8 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 87 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 120 3 7 29 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 120 3 6 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 87 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 120 3 5 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 87 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 120 3 4 29 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 120 3 3 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 87 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 120
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 120 3 2 29 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 87 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 120 3 1 29 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 87 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 87 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87 120)))))))))))))))))))))))))))))))))) (allB_succ' 35 86 120 (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 86 120 2 17 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 86 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 86 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 120 2 16 43 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 120 (accept_3_4 31 86 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 120 2 15 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 29
  86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 120 2 14 43 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 120 2 13 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 86 120 (accept_3_4 25 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86
  120 2 12 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  86 120 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 86 120 2 11 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 86 120 (Polychromatic418967fa.accept_18_3_14_12_1_1141 21 86 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 120 2 10 43 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 120 (accept_3_4 19 86 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 120 2 9 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 86 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 120 2 8 43 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 120
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 120 2 7 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 120 (accept_3_4 13 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  120 2 6 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 120 2 5 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 120 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 86 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 120 2 4 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 120 (accept_3_4 7 86 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 120 2 3 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 120 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 86 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 120 2 2 43 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 120
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 120 2 1 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 120 (accept_3_4 1 86 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  120))))))))))))))))))))))))))))))))))) (allB_succ' 36 85 120 (Eq.refl Bool.true) (allA_succ_of_gcd 35 85 120 5 7 17 24
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 85 120
  (Polychromatic418967fa.accept_9_7_4_3_1_204 34 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 120 (accept_3_5 32 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 120 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 85 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 120 5 6 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 120 (accept_3_5 29 85 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 85 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 120
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 120 (accept_3_5 26 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85
  120 5 5 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  85 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 85 120 (accept_3_5 23 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 85 120 (Polychromatic418967fa.accept_13_9_7_3_1_1531 22 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 120 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 85 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 120 5 4 17 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 120
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 120 (Polychromatic418967fa.accept_19_18_9_6_1_5815 18 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 120 (accept_3_5 17 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 85 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 120 5 3 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 120 (accept_3_5 14 85 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 120 (Polychromatic418967fa.accept_16_13_5_8_1_5814 13 85 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 120
  (Polychromatic418967fa.accept_16_12_5_8_1_2492 12 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 120 (accept_3_5 11 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  120 5 2 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 120 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 120 (accept_3_5 8 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 85 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 120 5 1 17 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 120
  (Polychromatic418967fa.accept_13_4_7_3_1_92 4 85 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 120 (Polychromatic418967fa.accept_16_3_5_8_1_4543 3 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 120 (accept_3_5 2 85 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 85 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 120)))))))))))))))))))))))))))))))))))) (allB_succ' 37 84 120
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 84 120 12 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 84 120 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 84 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 120 2 17 42 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 84 120 3 11 28 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 84 120 4 8 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 120
  (Polychromatic418967fa.accept_13_5_6_3_1_868 31 84 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 120 6 5 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 120 (Polychromatic418967fa.accept_16_13_4_8_1_4557 29 84 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 120 4 7 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 120 3 9 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 84 120 2 13 42 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 120 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 84 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 120 12 2 7 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 120
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 84 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 84 120 2 11 42 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 84 120 3 7 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 84 120 4 5 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 120 (Polychromatic418967fa.accept_16_3_4_8_1_3450 19 84 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 120 6 3 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 120 (Polychromatic418967fa.accept_16_1_4_8_1_3434 17 84 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 120 4 4 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 120 3 5 28 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 120 2 7 42 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 120
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 13 84 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 120 12 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 120 (Polychromatic418967fa.accept_16_11_4_8_1_3435 11 84 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 120 2 5 42 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 84 120 3 3 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 84 120 4 2 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 120 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7 84 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 120 6 1 14 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 120
  (Polychromatic418967fa.accept_13_5_6_3_1_868 5 84 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 120 4 1 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 84 120 3 1 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 84 120 2 1 42 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 120 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 84 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 120))))))))))))))))))))))))))))))))))))) (allB_succ' 38 83 120 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 83 120 (accept_3_4 37 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 83 120 (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 83 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 83 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 120 (accept_3_4 34 83 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 120 (accept_3_4 31 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 120 (Polychromatic418967fa.accept_16_13_3_8_1_2422 29 83 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 120 (accept_3_4 28 83 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 120 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 83
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 120 (accept_3_4 25 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 120 (accept_3_4 22 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 120 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 83 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 120
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 20 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 120 (accept_3_4 19 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 120 (Polychromatic418967fa.accept_19_18_7_6_1_4367 18 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 120 (accept_3_4 16 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 83 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 120 (accept_3_4 13 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 120 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 120 (accept_3_4 10 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 83 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 120
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 120 (accept_3_4 7 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  120 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 83 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 120 (accept_3_4 4 83 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 120 (Polychromatic418967fa.accept_17_3_15_1_1_3348 3 83 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 83
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 120 (accept_3_4 1 83 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83 120)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 82 120
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 82 120 2 19 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 82 120 (Polychromatic418967fa.accept_11_4_5_10_1_926 37 82 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 120 2 18 41 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 120 (accept_3_5 35 82 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 120 2 17 41 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 120
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 82 120 2 16 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 82 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 82 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 120 2 15 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 120 (accept_3_5 29 82 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 120 2 14 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 82 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 120 2 13 41 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 120
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 120 2 12 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 82 120 (accept_3_5 23 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82
  120 2 11 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  82 120 (Polychromatic418967fa.accept_17_4_14_1_1_1363 21 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 82 120 2 10 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 82 120 (Polychromatic418967fa.accept_25_19_7_20_1_5813 19 82 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 120 2 9 41 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 120 (accept_3_5 17 82 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 120 2 8 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 82 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 82 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 120 2 7 41 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 120
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 120 2 6 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 120 (accept_3_5 11 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82
  120 2 5 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  82 120 (Polychromatic418967fa.accept_18_9_10_12_1_5793 9 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 82 120 2 4 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 82 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 82 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 120 2 3 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 120 (accept_3_5 5 82 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 120 2 2 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 82 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 82 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 120 2 1 41 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 120
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 82 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 120))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 81 120 (Eq.refl Bool.true) (allA_succ_of_gcd 39
  81 120 3 13 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  38 81 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 81 120 (Polychromatic418967fa.accept_19_18_5_6_1_2004 37 81 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 120 3 12 27 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 120
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 35 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 120 (Polychromatic418967fa.accept_18_16_9_12_1_1182 34 81 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 120 3 11 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 120 (Polychromatic418967fa.accept_14_4_11_8_1_2034
  32 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 81 120 3 10 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 81 120 (Polychromatic418967fa.accept_17_12_13_1_1_4478 29 81 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 120 (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 81
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 120 3 9 27 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 120 (Polychromatic418967fa.accept_16_9_1_8_1_5766 25 81 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 120 3 8 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 120 (Polychromatic418967fa.accept_16_7_1_8_1_5796 23 81 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 120
  (Polychromatic418967fa.accept_18_4_9_12_1_1175 22 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 81 120 3 7 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 81 120 (Polychromatic418967fa.accept_16_4_1_8_1_835 20 81 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 81 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 120 3 6 27 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 120 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 81 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 120 3 5 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 120 (Polychromatic418967fa.accept_17_14_13_1_1_3356 14 81
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 120
  (Polychromatic418967fa.accept_21_13_18_15_1_2837 13 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 81 120 3 4 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 81 120 (Polychromatic418967fa.accept_18_11_9_12_1_4427 11 81 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 10 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 120 3 3 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 120 (Polychromatic418967fa.accept_21_8_18_15_1_5812 8 81 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 120 (Polychromatic418967fa.accept_16_7_1_8_1_5796 7 81 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 120 3 2 27 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 120 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 81 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 120 3 1 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 120 (Polychromatic418967fa.accept_17_2_13_1_1_3355 2 81 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 120
  (Polychromatic418967fa.accept_19_1_5_6_1_5811 1 81 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 120)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 80 120 (Eq.refl Bool.true) (allA_succ_of_gcd
  40 80 120 40 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 80 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 120 2 19 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 120 (accept_3_4 37 80 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 120 4 9 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 80 120 5 7 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 80 120 2 17 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 80 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 80 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 120 8 4 10 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 120 (accept_3_4 31 80 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 120 10 3 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 80 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 120 4 7 20 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 120
  (Polychromatic418967fa.accept_13_1_2_3_1_911 27 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 120 2 13 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 80 120 5 5 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 80 120 8 3 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 80 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 80 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 120 2 11 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 120 (Polychromatic418967fa.accept_18_3_8_12_1_3283
  21 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 120 20 1 4 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 120 (accept_3_4 19
  80 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 120 2 9 40 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 80 120
  (Polychromatic418967fa.accept_19_17_4_6_1_5810 17 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 80 120 8 2 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 80 120 5 3 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 80 120 2 7 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 120 (accept_3_4 13 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  120 4 3 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 80 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 120 10 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 80 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 120 8 1 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 120 (accept_3_4 7 80 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 120 2 3 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 5 80 120 5 1 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 4 80 120 4 1 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 80 120 (Polychromatic418967fa.accept_18_3_8_12_1_3283 3 80 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 120 2 1 40 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 120 (accept_3_4 1 80 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 80 120))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 79 120
  (Eq.refl Bool.true) (allA_succ_of_accept 41 79 120 (accept_3_5 41 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 79 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 120 (Polychromatic418967fa.accept_16_7_15_8_1_278 39 79 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 120 (accept_3_5 38 79 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 37
  79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 120
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 120 (accept_3_5 35 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 120 (accept_3_5 32 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 79 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 120
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 120 (accept_3_5 29 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 120 (accept_3_5 26 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 120 (Polychromatic418967fa.accept_16_9_15_8_1_3425 25 79 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 120
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 120 (accept_3_5 23 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 120 (Polychromatic418967fa.accept_18_3_7_12_1_1196 21 79 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 120 (accept_3_5 20 79 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 79 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 120
  (Polychromatic418967fa.accept_13_5_1_3_1_878 18 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 120 (accept_3_5 17 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 120 (Polychromatic418967fa.accept_19_16_3_6_1_1941 16 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 120 (accept_3_5 14 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 79 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 120
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 120 (accept_3_5 11 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 120 (Polychromatic418967fa.accept_16_9_15_8_1_3425 9 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 120 (accept_3_5 8 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 120 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 79 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 120 (accept_3_5 5 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  120 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 79 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 120 (accept_3_5 2 79 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 79 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 120)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 78
  120 (Eq.refl Bool.true) (allA_succ_of_gcd 42 78 120 6 7 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 78 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 120 2 20 39 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 120 3 13 26 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 120 2 19 39 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 120 6 6 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 78 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 120 2 17 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 120 3 11 26 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 78 120 2 16 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 31
  78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 120 6 5 13 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 120 2 14 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 78 120 3 9 26 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 78 120 2 13 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 78 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 120 6 4 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 78 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 120 2 11 39 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 120 3 7 26 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 120 2 10 39 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 120 6 3 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 78 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 120 2 8 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 120 3 5 26 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 120 2 7 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 78 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 120 6 2 13 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 120 2 5 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 78 120 3 3 26 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 78 120 2 4 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 78 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 120 6 1 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 78 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 120 2 2 39 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 120 3 1 26 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 120 2 1 39 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 78 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 120))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 77 120 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 77 120 (accept_3_4 43 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  77 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 77 120 (Polychromatic418967fa.accept_13_2_12_3_1_415 41 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 77 120 (accept_3_4 40 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 77 120 (Polychromatic418967fa.accept_21_18_14_15_1_5809 39 77 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 77 120 (accept_3_4 37 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  77 120 (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 77 120 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 120 (accept_3_4 34 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 77 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 120
  (Polychromatic418967fa.accept_17_15_9_1_1_3363 32 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 120 (accept_3_4 31 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 120 (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 120 (accept_3_4 28 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 120 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 77 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 120
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 120 (accept_3_4 25 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 120 (Polychromatic418967fa.accept_22_1_11_10_1_5808 23 77 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 120 (accept_3_4 22 77 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 120 (Polychromatic418967fa.accept_16_5_13_8_1_2454 21 77
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 120 (accept_3_4 19 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 120 (Polychromatic418967fa.accept_19_18_1_6_1_5807 18 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 120 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 120 (accept_3_4 16 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 77 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 120
  (Polychromatic418967fa.accept_19_14_1_6_1_5806 14 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 120 (accept_3_4 13 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 120 (Polychromatic418967fa.accept_16_12_13_8_1_2409 12 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 120 (accept_3_4 10 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 120 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 77 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 120
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 120 (accept_3_4 7 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  120 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 77 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 120 (Polychromatic418967fa.accept_16_5_13_8_1_2454 5 77 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 120 (accept_3_4 4 77 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 120 (Polychromatic418967fa.accept_16_3_13_8_1_1594 3 77 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 77
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 120 (accept_3_4 1 77 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 120)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  76 120 (Eq.refl Bool.true) (allA_succ_of_gcd 44 76 120 4 11 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 76 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 76 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 120 2 21 38 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 120 (accept_3_5 41
  76 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 120 4 10 19 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 120
  (Polychromatic418967fa.accept_16_7_12_8_1_2450 39 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 120 2 19 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 76 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 120 4 9 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 120 (accept_3_5 35 76 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 76 120 2 17 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 76 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 76 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 120 4 8 19 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 120
  (Polychromatic418967fa.accept_13_5_11_3_1_902 31 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 120 2 15 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 120 (accept_3_5 29 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  120 4 7 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 120 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 120 2 13 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 76 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 120 4 6 19 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 120 (accept_3_5 23 76 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 120 2 11 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 120 (Polychromatic418967fa.accept_13_8_11_3_1_3053
  21 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 120 4 5 19 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 120 2 9 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 120 (accept_3_5 17 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  120 4 4 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 120 2 7 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 120 (Polychromatic418967fa.accept_16_13_12_8_1_2451 13 76 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 120 4 3 19 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 120 (accept_3_5 11 76 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 120 2 5 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 76 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 120 4 2 19 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 120
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 120 2 3 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 120 (accept_3_5 5 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 120
  4 1 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  120 (Polychromatic418967fa.accept_16_3_12_8_1_808 3 76 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 76 120 2 1 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 76 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 76 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 120))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  75 120 (Eq.refl Bool.true) (allA_succ_of_gcd 45 75 120 15 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 120 (Polychromatic418967fa.accept_16_12_11_8_1_832 44 75 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 120
  (Polychromatic418967fa.accept_18_7_3_12_1_3241 43 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 75 120 3 14 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 120 5 8 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 75 120 3 13 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 75 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 120
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 120 3 12 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 75 120 5 7 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 120 3 11 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 120 15 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 120 (Polychromatic418967fa.accept_16_13_11_8_1_2449 29 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 120 (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 75
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 120 3 9 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 120
  (Polychromatic418967fa.accept_18_8_3_12_1_3247 26 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 75 120 5 5 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 75 120 3 8 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 120 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 120 (Polychromatic418967fa.accept_19_3_18_6_1_3112 22 75
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 120 3 7 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 75 120 5 4 15 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 120
  (Polychromatic418967fa.accept_11_8_9_10_1_503 19 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 120 3 6 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 120 (Polychromatic418967fa.accept_27_16_21_12_1_5805 16 75
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 120 15 1 5 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 120
  (Polychromatic418967fa.accept_18_14_3_12_1_3249 14 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 120 3 4 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 75 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 120 5 2 15 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 75 120 3 3 25 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 120
  (Polychromatic418967fa.accept_11_8_9_10_1_503 8 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 120 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 120 3 2 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 75 120 5 1 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 75 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 120 3 1 25 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 120
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 75 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 120 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 75 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75 120)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 74 120
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 74 120 2 23 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 74 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 74 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 120 2 22 37 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 120 (accept_3_4 43 74 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 120 2 21 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 74 120 2 20 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 74 120 (Polychromatic418967fa.accept_14_11_4_8_1_664 39 74 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 120 2 19 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 120 (accept_3_4 37 74 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 120 2 18 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 74 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 120 2 17 37 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 120 2 16 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 74 120 (accept_3_4 31 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74
  120 2 15 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  74 120 (Polychromatic418967fa.accept_17_12_6_1_1_4517 29 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 74 120 2 14 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 74 120 (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 74 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 120 2 13 37 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 120 (accept_3_4 25 74 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 120 2 12 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 74 120 2 11 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 74 120 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 74 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 120 2 10 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 120 (accept_3_4 19 74 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 120 2 9 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 74 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 74 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 120 2 8 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 120
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 120 2 7 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 120 (accept_3_4 13 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  120 2 6 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 120 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 120 2 5 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 120 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 74 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 120 2 4 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 120 (accept_3_4 7 74 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 120 2 3 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 74 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 120 2 2 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 120 2 1 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 120 (accept_3_4 1 74 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  120))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 73 120 (Eq.refl Bool.true) (allA_succ_of_accept 47
  73 120 (accept_3_5 47 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 46 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 73 120 (Polychromatic418967fa.accept_19_7_16_6_1_4400 45 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 120 (accept_3_5 44 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 73 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 42
  73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 120 (accept_3_5 41 73
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 120
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 73 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 120 (accept_3_5 38 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 73 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 120 (Polychromatic418967fa.accept_11_3_7_10_1_180
  36 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 120 (accept_3_5 35
  73 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 120
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 73 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 120 (accept_3_5 32 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 73 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 30
  73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 120 (accept_3_5 29 73
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 120
  (Polychromatic418967fa.accept_16_12_9_8_1_2508 28 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 73 120 (Polychromatic418967fa.accept_19_8_16_6_1_5804 27 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 120 (accept_3_5 26 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 73 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 24
  73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 120 (accept_3_5 23 73
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 120
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 73 120 (Polychromatic418967fa.accept_17_4_5_1_1_5776 21 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 120 (accept_3_5 20 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 73 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 18
  73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 120 (accept_3_5 17 73
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 120 (Polychromatic418967fa.accept_7_2_3_1_1_10
  16 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 120
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 120 (accept_3_5 14 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 120 (accept_3_5 11 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 120 (Polychromatic418967fa.accept_19_10_16_6_1_5773 10 73 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 120 (accept_3_5 8 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 120 (accept_3_5 5 73 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 120 (Polychromatic418967fa.accept_11_3_7_10_1_180 3
  73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 120 (accept_3_5 2 73 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 120 (Polychromatic418967fa.accept_16_1_9_8_1_2438 1
  73 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  120)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 72 120 (Eq.refl Bool.true) (allA_succ_of_gcd 48 72
  120 24 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  72 120 (Polychromatic418967fa.accept_13_8_7_3_1_430 47 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 72 120 2 23 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 72 120 3 15 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 72 120 4 11 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 72 120 (Polychromatic418967fa.accept_13_4_7_3_1_92 43 72 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 120 6 7 12 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 120 8 5 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 72 120 3 13 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 72 120 2 19 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 72 120 (Polychromatic418967fa.accept_13_11_7_3_1_894 37 72 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 120 12 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 120 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 72 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 120 2 17 36 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 120 3 11 24 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 120 8 4 9 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 120
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 120 6 5 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 120 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 72 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 120 4 7 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 120 3 9 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 120 2 13 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 120 (Polychromatic418967fa.accept_17_8_4_1_1_5730 25 72 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 120 24 1 3 5 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 120
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 72 120 2 11 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 72 120 3 7 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 72 120 4 5 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 120 (Polychromatic418967fa.accept_21_19_9_15_1_4217 19 72 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 120 6 3 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 120 8 2 9 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 72 120 3 5 24 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 72 120 2 7 36 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 120 12 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 120 (Polychromatic418967fa.accept_13_11_7_3_1_894 11 72 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 120 2 5 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 120 3 3 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 120 8 1 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 120 (Polychromatic418967fa.accept_21_7_9_15_1_5803 7 72 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 120 6 1 12 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 120
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 72 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 120 4 1 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 72 120 3 1 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 72 120 2 1 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 120 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 72 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72 120))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 71
  120 (Eq.refl Bool.true) (allA_succ_of_accept 49 71 120 (accept_3_4 49 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 71 120 (Polychromatic418967fa.accept_11_4_5_10_1_926 48 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 71 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 120 (accept_3_4 46 71 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 120 (Polychromatic418967fa.accept_18_9_17_12_1_462
  45 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 120
  (Polychromatic418967fa.accept_13_5_6_3_1_868 44 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 120 (accept_3_4 43 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 120 (accept_3_4 40 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 120 (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 71 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 120
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 120 (accept_3_4 37 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 120 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 120 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 120 (accept_3_4 34 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 71 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 120
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 120 (accept_3_4 31 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 120 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 120 (accept_3_4 28 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 120 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 71 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 120
  (Polychromatic418967fa.accept_11_4_5_10_1_926 26 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 120 (accept_3_4 25 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 120 (accept_3_4 22 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 120 (Polychromatic418967fa.accept_14_7_1_8_1_2873 21 71 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 120
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 120 (accept_3_4 19 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 120 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 120 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 71 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 120 (accept_3_4 16 71 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 71 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 120
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 120 (accept_3_4 13 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 120 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 120 (accept_3_4 10 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 120 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 71 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 120
  (Polychromatic418967fa.accept_19_8_14_6_1_5802 8 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 120 (accept_3_4 7 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  120 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 120 (accept_3_4 4 71 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 120 (Polychromatic418967fa.accept_21_3_8_15_1_4301 3 71 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  71 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 120 (accept_3_4 1 71 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 120))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 70 120 (Eq.refl Bool.true) (allA_succ_of_gcd 50 70 120 10 5 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 120
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 70 120 2 24 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 70 120 (accept_3_5 47 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70
  120 2 23 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 70
  120 5 9 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 70
  120 2 22 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  70 120 (Polychromatic418967fa.accept_21_1_7_15_1_4259 43 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 70 120 2 21 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 70 120 (accept_3_5 41 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 70 120 10 4 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 70 120 (Polychromatic418967fa.accept_21_18_7_15_1_2877 39 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 120 2 19 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 37
  70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 120 2 18 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 120 5 7 14 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 70 120 2 17 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 120
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 120 2 16 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 70 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 120 10 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 120 (accept_3_5 29 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 70 120 2 14 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 70 120 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 70 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 120 2 13 35 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 70 120 5 5 14 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 70 120 2 12 35 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 120 (accept_3_5 23 70 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 120 2 11 35 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 120
  (Polychromatic418967fa.accept_13_8_5_3_1_427 21 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 120 10 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 120 2 9 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 120 (accept_3_5 17 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 120 2 8 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 70 120 5 3 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 70 120 2 7 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 70 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 120 2 6 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 120 (accept_3_5 11 70 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 120 10 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 70 120 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 70 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 120 2 4 35 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 120
  (Polychromatic418967fa.accept_19_7_13_6_1_1914 7 70 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 120 2 3 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 70 120 5 1 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 70 120 2 2 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 70 120 (Polychromatic418967fa.accept_17_3_2_1_1_1367 3 70 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 120 2 1 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 70 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  120))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 69 120 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  69 120 3 17 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 69 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 69 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 69 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 120 3 16 23 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 120 3 15 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 44
  69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 120
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 120 3 14 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 69 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 120 3 13 23 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 120 3 12 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 120
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 120 3 11 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 69 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 120 3 10 23 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 120 3 9 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 69 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 120
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 120 3 8 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 69 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 120 3 7 23 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 120 3 6 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 69 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 120 3 5 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 69 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 120 3 4 23 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 120 3 3 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 69 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 120
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 120 3 2 23 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 69 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 120 3 1 23 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 69 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 69 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 120)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 68
  120 (Eq.refl Bool.true) (allA_succ_of_gcd 52 68 120 4 13 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 68 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 120 2 25 34 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 120 (accept_3_4 49
  68 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 120 4 12 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 120 2 23 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 68 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 120 4 11 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 120 (accept_3_4 43 68 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 120 2 21 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 68 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 120 4 10 17 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 120
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 120 2 19 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 120 (accept_3_4 37 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  120 4 9 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 120 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 120 2 17 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 68 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 120 4 8 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 120 (accept_3_4 31 68 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 120 2 15 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 29
  68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 120 4 7 17 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 120
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 120 2 13 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 120 (accept_3_4 25 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68
  120 4 6 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  68 120 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 68 120 2 11 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 68 120 (Polychromatic418967fa.accept_16_5_4_8_1_1560 21 68 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 120 4 5 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 120 (accept_3_4 19 68 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 120 2 9 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 68 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 120 4 4 17 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 120
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 120 2 7 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 120 (accept_3_4 13 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  120 4 3 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 120 2 5 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 120 (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 68 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 120 4 2 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 120 (accept_3_4 7 68 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 120 2 3 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 120 (Polychromatic418967fa.accept_16_5_4_8_1_1560 5 68 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 120 4 1 17 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 120 2 1 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 120 (accept_3_4 1 68 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  120))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 67 120 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 67 120 (accept_3_5 53 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 120 (accept_3_5 50 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 120 (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 120
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 120 (accept_3_5 47 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 120 (accept_3_5 44 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 120
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 120 (accept_3_5 41 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 120 (Polychromatic418967fa.accept_17_5_16_1_1_3358 39 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 120 (accept_3_5 38 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 67 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 120
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 120 (accept_3_5 35 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 120 (accept_3_5 32 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 120
  (Polychromatic418967fa.accept_21_9_4_15_1_5801 30 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 120 (accept_3_5 29 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 120 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 120 (accept_3_5 26 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 120 (accept_3_5 23 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 120 (Polychromatic418967fa.accept_13_9_2_3_1_3027 22 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 120 (Polychromatic418967fa.accept_16_5_3_8_1_4555 21 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 120 (accept_3_5 20 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 120
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 120 (accept_3_5 17 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 120 (accept_3_5 14 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 120 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 120 (accept_3_5 11 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 120 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 120 (accept_3_5 8 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 120
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 120 (accept_3_5 5 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  120 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 67 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 120 (accept_3_5 2 67 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 67 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  120)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 66 120 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 66 120 6 9 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 66 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 120 2 26 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 66 120 3 17 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 66 120 2 25 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 120 (Polychromatic418967fa.accept_21_7_3_15_1_5800
  49 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 120 6 8 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 120
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 120 2 23 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 66 120 3 15 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 66 120 2 22 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 120 (Polychromatic418967fa.accept_13_4_1_3_1_3058 43 66 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 120 6 7 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 120 (Polychromatic418967fa.accept_13_2_1_3_1_419 41 66 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 120 2 20 33 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 120 3 13 22 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 120 2 19 33 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 120 6 6 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 120 (Polychromatic418967fa.accept_19_16_9_6_1_5799 35 66 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 120 2 17 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 120 3 11 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 120 2 16 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 120 (Polychromatic418967fa.accept_13_5_1_3_1_878 31
  66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 120 6 5 11 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 120
  (Polychromatic418967fa.accept_17_12_15_1_1_5798 29 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 120 2 14 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 66 120 3 9 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 66 120 2 13 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 66 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 120 6 4 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 66 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 120 2 11 33 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 120 3 7 22 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 120 2 10 33 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 120
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 120 6 3 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 120 (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 66 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 120 2 8 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 120 3 5 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 120 2 7 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 120 (Polychromatic418967fa.accept_19_13_9_6_1_4393 13 66 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 120 6 2 11 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 120 2 5 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 66 120 3 3 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 66 120 2 4 33 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 120 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 66 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 120 6 1 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 120 2 2 33 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 120 3 1 22 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 120 2 1 33 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 120
  (Polychromatic418967fa.accept_21_1_3_15_1_5797 1 66 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 120))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 65 120 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 65 120 5 11 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 120 (Polychromatic418967fa.accept_19_16_8_6_1_4407 54 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 65 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 120 (accept_3_4 52 65 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 51
  65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 120 5 10 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 120 (accept_3_4 49
  65 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 120 (Polychromatic418967fa.accept_16_15_1_8_1_1585 47 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 120 (accept_3_4 46 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 120 5 9 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 120 (accept_3_4 43 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 65 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 120 5 8 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 120 (Polychromatic418967fa.accept_16_7_1_8_1_5796 39 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 65 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 120 (accept_3_4 37 65 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 120 (Polychromatic418967fa.accept_16_4_1_8_1_835
  36 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 120 5 7 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 120 (accept_3_4 34
  65 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 120
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 120 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 120 (accept_3_4 31 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 65 120 5 6 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 65 120 (Polychromatic418967fa.accept_14_1_9_8_1_2863 29 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 120 (accept_3_4 28 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 65 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 120
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 120 5 5 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 120 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 65 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 120 (accept_3_4 22 65 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 120 (Polychromatic418967fa.accept_17_4_14_1_1_1363
  21 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 120 5 4 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 120 (accept_3_4 19
  65 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 120
  (Polychromatic418967fa.accept_21_18_2_15_1_5737 18 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 120 (accept_3_4 16 65 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 120 5 3 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 120 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 120 (accept_3_4 13 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 120 (Polychromatic418967fa.accept_16_12_1_8_1_5767 12 65 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 120
  (Polychromatic418967fa.accept_22_11_21_10_1_5795 11 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 65 120 5 2 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 65 120 (Polychromatic418967fa.accept_16_9_1_8_1_5766 9 65 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 8
  65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 120 (accept_3_4 7 65 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 120 5 1 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 120 (accept_3_4 4 65
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 120 (Polychromatic418967fa.accept_7_3_2_1_1_225
  3 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 120
  (Polychromatic418967fa.accept_19_2_8_6_1_1905 2 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 120 (accept_3_4 1 65 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  120)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 64 120 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 64 120 8 7 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 120 (Polychromatic418967fa.accept_26_3_12_16_1_5794 55 64 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 120 2 27 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 120 (accept_3_5 53 64 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 120 4 13 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 64 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 120 2 25 32 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 120
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 120 8 6 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 120 (accept_3_5 47 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  120 2 23 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 120 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 120 4 11 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 64 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 120 2 21 32 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 120 (accept_3_5 41 64 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 120 8 5 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 120 (Polychromatic418967fa.accept_19_1_7_6_1_1959
  39 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 120 2 19 32 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 120
  (Polychromatic418967fa.accept_19_18_7_6_1_4367 37 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 120 4 9 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 120 (accept_3_5 35 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  120 2 17 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 120 8 4 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 64 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 64 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 120 2 15 32 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 120 (accept_3_5 29 64 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 120 4 7 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 120 (Polychromatic418967fa.accept_18_9_10_12_1_5793 27 64
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 120 2 13 32 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 120
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 120 8 3 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 120 (accept_3_5 23 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  120 2 11 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  64 120 (Polychromatic418967fa.accept_22_21_20_10_1_5792 21 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 120 4 5 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 120 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 64 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 120 2 9 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 120 (accept_3_5 17 64 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 120 8 2 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 64 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 64 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 120 2 7 32 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 120
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 120 4 3 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 120 (accept_3_5 11 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  120 2 5 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 120 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 120 8 1 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 64 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 120 2 3 32 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 120 (accept_3_5 5 64 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 120 4 1 16 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 120 (Polychromatic418967fa.accept_19_3_7_6_1_5791 3 64 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 120 2 1 32 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 120
  (Polychromatic418967fa.accept_11_1_9_10_1_184 1 64 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 120))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 63 120 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 63 120 3 19 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 120 (Polychromatic418967fa.accept_23_10_17_5_1_5790 56 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 120 (Polychromatic418967fa.accept_14_13_7_8_1_677 55 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 120 3 18 21 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 120
  (Polychromatic418967fa.accept_11_9_8_10_1_934 53 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 120 (Polychromatic418967fa.accept_16_4_15_8_1_2413 52 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 120 3 17 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 120 (Polychromatic418967fa.accept_17_16_12_1_1_5785
  50 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 120
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 49 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 120 3 16 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 120 (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 120 (Polychromatic418967fa.accept_13_7_11_3_1_1540 46 63
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 120 3 15 21 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 120
  (Polychromatic418967fa.accept_13_5_11_3_1_902 44 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 120 (Polychromatic418967fa.accept_14_1_7_8_1_2063 43 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 120 3 14 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 120 (Polychromatic418967fa.accept_13_2_11_3_1_873
  41 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 120
  (Polychromatic418967fa.accept_13_1_11_3_1_901 40 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 120 3 13 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 120 (Polychromatic418967fa.accept_27_11_9_12_1_5789 38 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 120 (Polychromatic418967fa.accept_23_14_17_5_1_5788 37 63
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 120 3 12 21 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 120
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 35 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 120 (Polychromatic418967fa.accept_13_8_11_3_1_3053 34 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 120 3 11 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 120 (Polychromatic418967fa.accept_17_15_12_1_1_3365
  32 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 120
  (Polychromatic418967fa.accept_11_9_8_10_1_934 31 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 120 3 10 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 120 (Polychromatic418967fa.accept_14_1_7_8_1_2063 29 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 120 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 120 3 9 21 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 120
  (Polychromatic418967fa.accept_25_1_13_20_1_5787 26 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 120 (Polychromatic418967fa.accept_16_9_15_8_1_3425 25 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 120 3 8 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 120 (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 63
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 120
  (Polychromatic418967fa.accept_18_4_9_12_1_1175 22 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 120 3 7 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 120 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 120 (Polychromatic418967fa.accept_27_19_9_12_1_5786 19 63
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 120 3 6 21 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 120
  (Polychromatic418967fa.accept_16_1_15_8_1_2411 17 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 120 (Polychromatic418967fa.accept_17_16_12_1_1_5785 16 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 120 3 5 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 120 (Polychromatic418967fa.accept_13_1_11_3_1_901 14 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 120
  (Polychromatic418967fa.accept_14_13_7_8_1_677 13 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 120 3 4 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 120 (Polychromatic418967fa.accept_18_11_9_12_1_4427 11 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 120 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 63
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 120 3 3 21 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 120
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 120 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 120 3 2 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 120 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 120
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 4 63 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 120 3 1 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 120 (Polychromatic418967fa.accept_13_2_11_3_1_873 2 63 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 120 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 63 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  120)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 62 120 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 62 120 2 29 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 120 (Polychromatic418967fa.accept_18_3_8_12_1_3283 57 62 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 120 2 28 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 120 (accept_3_4 55 62 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 120 2 27 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 120 (Polychromatic418967fa.accept_19_15_5_6_1_5760 53 62 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 120 2 26 31 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 120 2 25 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 120 (accept_3_4 49 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  120 2 24 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 120 2 23 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 120 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 62 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 120 2 22 31 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 120 (accept_3_4 43 62 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 120 2 21 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 120
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 120 2 20 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 120 (Polychromatic418967fa.accept_18_3_8_12_1_3283 39 62 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 120 2 19 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 120 (accept_3_4 37 62 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 120 2 18 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 120 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 62 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 120 2 17 31 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 120 2 16 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 120 (accept_3_4 31 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  120 2 15 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 120 2 14 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 120 (Polychromatic418967fa.accept_17_10_11_1_1_5784 27 62 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 120 2 13 31 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 120 (accept_3_4 25 62 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 120 2 12 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 120 2 11 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 120 (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 62 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 120 2 10 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 120 (accept_3_4 19 62 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 120 2 9 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 120 (Polychromatic418967fa.accept_22_17_18_10_1_5783 17 62 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 120 2 8 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 120
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 120 2 7 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 120 (accept_3_4 13 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  120 2 6 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 120 2 5 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 62 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 120 2 4 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 120 (accept_3_4 7 62 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 120 2 3 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 62 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 120 2 2 31 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 120
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 120 2 1 31 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 120 (accept_3_4 1 62 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  120))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 61 120 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 61 120 (accept_3_5 59 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 120 (Polychromatic418967fa.accept_13_5_9_3_1_870 57 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 120 (accept_3_5 56 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 61 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 120
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 54 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 120 (accept_3_5 53 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 120 (accept_3_5 50 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 61 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 120
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 120 (accept_3_5 47 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 120 (accept_3_5 44 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 120 (Polychromatic418967fa.accept_16_11_13_8_1_1578 43 61 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 120
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 120 (accept_3_5 41 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 120 (accept_3_5 38 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 61 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 120
  (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 120 (accept_3_5 35 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 120 (accept_3_5 32 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 61 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 120
  (Polychromatic418967fa.accept_21_9_19_15_1_5782 30 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 120 (accept_3_5 29 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 120 (accept_3_5 26 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 120 (accept_3_5 23 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 120 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 120 (accept_3_5 20 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 61 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 120
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 120 (accept_3_5 17 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 120 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 120 (accept_3_5 14 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 120
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 120 (accept_3_5 11 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 120 (Polychromatic418967fa.accept_17_9_10_1_1_3345 9 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 120 (accept_3_5 8 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 120 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 61 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 120
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 120 (accept_3_5 5 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  120 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 120 (accept_3_5 2 61 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 61 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 120))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 120 (allA_succ_of_accept 59 60 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 60 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 120 2 29 30 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 60 120 3 19 20 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 60 120 4 14 15 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 60 120 5 11 12 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 120 6 9 10 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 120
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 120 4 13 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 60 120 3 17 20 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 60 120 10 5 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 60 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 120 12 4 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 60 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 120 2 23 30 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 120 15 3 4 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 120 4 11 15 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 120
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 120 6 7 10 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 60 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 120 20 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 120 3 13 20 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 120 2 19 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 60 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 120 12 3 5 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 120 5 7 12 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 120 2 17 30 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 120 3 11 20 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 120 4 8 15 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 120 30 1 2 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 60 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 120 4 7 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 120 3 9 20 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 120 2 13 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 120 5 5 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 120 12 2 5 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 60 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 120 2 11 30 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 120 3 7 20 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 120 20 1 3 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 120 6 3 10 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 120 4 4 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 120 15 1 4 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 120 2 7 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 60 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 120 12 1 5 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 60 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 120 10 1 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 60 120 3 3 20 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 60 120 4 2 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 60 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 120 6 1 10 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 120 5 1 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 120 4 1 15 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 120 3 1 20 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 120 2 1 30 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 60 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  120)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 120 (allA_succ_of_accept 58 59 120
  (accept_3_4 58 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 120
  (Polychromatic418967fa.accept_38_19_21_6_1_5781 57 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 120 (accept_3_4 55 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 120 (accept_3_4 52 59
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 120 (Polychromatic418967fa.accept_7_2_3_1_1_10
  51 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 120
  (Polychromatic418967fa.accept_13_11_7_3_1_894 50 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 120 (accept_3_4 49 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 120 (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 120 (accept_3_4 46 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 120 (Polychromatic418967fa.accept_16_13_11_8_1_2449 45 59 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 120 (accept_3_4 43 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 120 (Polychromatic418967fa.accept_17_7_8_1_1_1373 41 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 120 (accept_3_4 40 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 59 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 120 (accept_3_4 37 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 120 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 120 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 120 (accept_3_4 34 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 59 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 120 (accept_3_4 31 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 120 (accept_3_4 28 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 120 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 59 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 120
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 120 (accept_3_4 25 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 120 (accept_3_4 22 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 120 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 59 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 120 (accept_3_4 19 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 120 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 120 (accept_3_4 16 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 59 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 120
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 120 (accept_3_4 13 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 120 (accept_3_4 10 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 59 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 120
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 120 (accept_3_4 7 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  120 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 59 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 120 (accept_3_4 4 59 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 120 (Polychromatic418967fa.accept_16_3_11_8_1_830 3 59 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 59
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 120 (accept_3_4 1 59 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 120)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 120 (allA_succ_of_accept 57 58 120 (Polychromatic418967fa.accept_13_5_6_3_1_868 57 58 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 120 2 28 29 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 58 120 2 27 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 58 120 (accept_3_5 53 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58
  120 2 26 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  58 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 58 120 2 25 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 58 120 (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 58 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 120 2 24 29 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 120 (accept_3_5 47 58 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 120 2 23 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 120
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 58 120 2 22 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 58 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 58 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 120 2 21 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 120 (accept_3_5 41 58 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 120 2 20 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 120 (Polychromatic418967fa.accept_21_18_16_15_1_2864 39 58
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 120 2 19 29 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 120
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 120 2 18 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 58 120 (accept_3_5 35 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58
  120 2 17 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  58 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 58 120 2 16 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 58 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 58 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 120 2 15 29 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 120 (accept_3_5 29 58 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 120 2 14 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 58 120 2 13 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 58 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 58 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 120 2 12 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 120 (accept_3_5 23 58 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 120 2 11 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 120 (Polychromatic418967fa.accept_19_2_1_6_1_5780 21 58 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 120 2 10 29 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 120
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 120 2 9 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 120 (accept_3_5 17 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  120 2 8 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 120 2 7 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 58 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 58 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 120 2 6 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 120 (accept_3_5 11 58 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 120 2 5 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 58 120 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 58 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 58 120 2 4 29 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 120
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 58 120 2 3 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 58 120 (accept_3_5 5 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 120
  2 2 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58
  120 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 58 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 58 120 2 1 29 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 58 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 58 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 58 120)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  57 120 (allA_succ_of_accept 56 57 120 (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 57 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 120 (Polychromatic418967fa.accept_16_7_9_8_1_829
  55 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 120 3 18 19 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 120
  (Polychromatic418967fa.accept_13_1_5_3_1_888 53 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 57 120 (Polychromatic418967fa.accept_16_4_9_8_1_2509 52 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 120 3 17 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 120 (Polychromatic418967fa.accept_13_11_5_3_1_889
  50 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 120
  (Polychromatic418967fa.accept_14_7_1_8_1_2873 49 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 57 120 3 16 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 57 120 (Polychromatic418967fa.accept_13_8_5_3_1_427 47 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 120 (Polychromatic418967fa.accept_17_12_6_1_1_4517 46 57
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 120 3 15 19 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 120
  (Polychromatic418967fa.accept_14_2_1_8_1_650 44 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 120 (Polychromatic418967fa.accept_18_7_3_12_1_3241 43 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 120 3 14 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 120 (Polychromatic418967fa.accept_13_2_5_3_1_406 41
  57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 120
  (Polychromatic418967fa.accept_13_1_5_3_1_888 40 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 57 120 3 13 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 57 120 (Polychromatic418967fa.accept_18_2_3_12_1_1155 38 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 120 (Polychromatic418967fa.accept_13_11_5_3_1_889 37 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 120 3 12 19 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 120
  (Polychromatic418967fa.accept_13_9_5_3_1_428 35 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 120 (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 120 3 11 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 120 (Polychromatic418967fa.accept_13_6_5_3_1_426 32
  57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 120
  (Polychromatic418967fa.accept_16_15_9_8_1_2440 31 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 57 120 3 10 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 57 120 (Polychromatic418967fa.accept_17_12_6_1_1_4517 29 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 120 (Polychromatic418967fa.accept_13_2_5_3_1_406 28 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 120 3 9 19 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 120
  (Polychromatic418967fa.accept_18_8_3_12_1_3247 26 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 120 (Polychromatic418967fa.accept_18_7_3_12_1_3241 25 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 120 3 8 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 120 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 120
  (Polychromatic418967fa.accept_13_9_5_3_1_428 22 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 57 120 3 7 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 57 120 (Polychromatic418967fa.accept_16_4_9_8_1_2509 20 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 120 (Polychromatic418967fa.accept_13_6_5_3_1_426 19 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 120 3 6 19 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 120
  (Polychromatic418967fa.accept_16_1_9_8_1_2438 17 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 120 (Polychromatic418967fa.accept_14_2_1_8_1_650 16 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 120 3 5 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 120 (Polychromatic418967fa.accept_13_1_5_3_1_888 14 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 120
  (Polychromatic418967fa.accept_18_13_3_12_1_3207 13 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 57 120 3 4 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 57 120 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 120 (Polychromatic418967fa.accept_23_10_11_5_1_5779 10 57
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 120 3 3 19 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 120
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 120 (Polychromatic418967fa.accept_14_7_1_8_1_2873 7 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 120 3 2 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 120 (Polychromatic418967fa.accept_17_5_6_1_1_5735 5 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 120
  (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 57 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 57 120 3 1 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 57 120 (Polychromatic418967fa.accept_13_2_5_3_1_406 2 57 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 120 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 57 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  120))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 120 (allA_succ_of_accept 55 56 120
  (accept_3_4 55 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 56 120 2 27 28 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 56 120
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 56 120 4 13 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 56 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 56 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 120 2 25 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 120 (accept_3_4 49 56 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 120 8 6 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 56 120 (Polychromatic418967fa.accept_19_9_18_6_1_5778 47 56 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 120 2 23 28 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 120
  (Polychromatic418967fa.accept_19_7_18_6_1_3095 45 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 120 4 11 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 56 120 (accept_3_4 43 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  120 2 21 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 120 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 56 120 8 5 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 56 120 (Polychromatic418967fa.accept_18_3_2_12_1_5751 39 56 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 120 2 19 28 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 120 (accept_3_4 37 56 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 120 4 9 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 56 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 56 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 120 2 17 28 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 120
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 120 8 4 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 120 (accept_3_4 31 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  120 2 15 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  56 120 (Polychromatic418967fa.accept_21_8_14_15_1_5777 29 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 120 4 7 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 120 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 56 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 120 2 13 28 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 120 (accept_3_4 25 56 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 120 8 3 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 120 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 56 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 120 2 11 28 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 120
  (Polychromatic418967fa.accept_17_4_5_1_1_5776 21 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 120 4 5 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 120 (accept_3_4 19 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  120 2 9 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 120 8 2 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 56 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 120 2 7 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 120 (accept_3_4 13 56 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 120 4 3 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 120 (Polychromatic418967fa.accept_19_11_18_6_1_3113 11 56 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 120 2 5 28 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 120
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 120 8 1 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 120 (accept_3_4 7 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 120
  2 3 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  120 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 56 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 120 4 1 14 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 120 (Polychromatic418967fa.accept_18_3_2_12_1_5751 3 56 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 120 2 1 28 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 120 (accept_3_4 1 56 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 120)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 120
  (allA_succ_of_accept 54 55 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 120 (accept_3_5 53 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 120 5 10 11 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 120
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 120 (Polychromatic418967fa.accept_17_14_4_1_1_3341 48 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 120 (accept_3_5 47 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 120 (Polychromatic418967fa.accept_19_8_17_6_1_5728 46 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 120 5 9 11 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 120 (accept_3_5 44 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 55 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 120
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 120 (accept_3_5 41 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  120 5 8 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 120 (Polychromatic418967fa.accept_17_5_4_1_1_3369 39 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 120 (accept_3_5 38 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 120 (Polychromatic418967fa.accept_16_4_7_8_1_5753 36 55 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 120 5 7 11 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 120
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 120 (accept_3_5 32 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 120 5 6 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 120 (accept_3_5 29 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 120 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 120
  (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 120 (accept_3_5 26 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  120 5 5 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 120 (accept_3_5 23 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 120 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 55
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 120 5 4 11 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 120 (Polychromatic418967fa.accept_19_18_17_6_1_5775 18 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 120 (accept_3_5 17 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 120 5 3 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 120 (accept_3_5 14 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 55 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 120 (accept_3_5 11 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  120 5 2 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 120 (accept_3_5 8 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 55 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 120 5 1 11 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 120
  (Polychromatic418967fa.accept_9_4_1_3_1_190 4 55 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 120 (Polychromatic418967fa.accept_18_3_1_12_1_4419 3 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 120 (accept_3_5 2 55 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 120 (Polychromatic418967fa.accept_16_1_7_8_1_3422 1 55 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 120)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 120 (allA_succ_of_accept 53 54 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 54 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 120 2 26 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 54 120 3 17 18 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 54 120 2 25 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 120
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 120 6 8 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 120 (Polychromatic418967fa.accept_19_9_16_6_1_5774 47 54 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 120 2 23 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 120 3 15 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 120 2 22 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 120 (Polychromatic418967fa.accept_17_9_3_1_1_2275
  43 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 120 6 7 9 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 120
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 120 2 20 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 54 120 3 13 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 54 120 2 19 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 54 120 (Polychromatic418967fa.accept_13_11_2_3_1_883 37 54 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 120 6 6 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 120 (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 54 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 120 2 17 27 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 54 120 3 11 18 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 54 120 2 16 27 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 120 6 5 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 120 (Polychromatic418967fa.accept_19_10_16_6_1_5773 29 54 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 120 2 14 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 120 3 9 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 120 2 13 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 25
  54 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 120 6 4 9 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 120
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 120 2 11 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 54 120 3 7 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 54 120 2 10 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 120 (Polychromatic418967fa.accept_17_2_3_1_1_2244 19 54 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 120 6 3 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 54 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 120 2 8 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 120 3 5 18 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 120 2 7 27 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 120
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 120 6 2 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 54 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 120 2 5 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 120 3 3 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 120 2 4 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 120 (Polychromatic418967fa.accept_19_7_16_6_1_4400 7 54 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 120 6 1 9 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 120
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 54 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 54 120 2 2 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 54 120 3 1 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 54 120 2 1 27 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 120 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 54 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 120)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  120 (allA_succ_of_accept 52 53 120 (accept_3_4 52 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 50 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 120 (accept_3_4 49 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 120 (Polychromatic418967fa.accept_19_10_15_6_1_5772 48 53 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 120 (accept_3_4 46 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 120 (Polychromatic418967fa.accept_13_5_1_3_1_878 44 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 120 (accept_3_4 43 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 53 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 120
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 120 (accept_3_4 40 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 120 (Polychromatic418967fa.accept_26_13_1_16_1_5771 39 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 120 (accept_3_4 37 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 120 (Polychromatic418967fa.accept_16_4_5_8_1_2425 36 53 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 120
  (Polychromatic418967fa.accept_16_3_5_8_1_4543 35 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 120 (accept_3_4 34 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 120 (accept_3_4 31 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 120 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 53 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 120
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 120 (accept_3_4 28 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 120 (Polychromatic418967fa.accept_16_11_5_8_1_2427 27 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 120 (accept_3_4 25 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 120
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 120 (accept_3_4 22 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 120 (Polychromatic418967fa.accept_19_2_15_6_1_4408 21 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 120 (accept_3_4 19 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 120 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 53 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 120 (accept_3_4 16 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 120 (accept_3_4 13 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 120
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 120 (accept_3_4 10 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 120 (Polychromatic418967fa.accept_18_9_17_12_1_462 9 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 120 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 120 (accept_3_4 7 53 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 53 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 120 (accept_3_4 4 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  120 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 53 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 120 (accept_3_4 1 53 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 120))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 120
  (allA_succ_of_accept 51 52 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 52 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 120 2 25 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 49
  52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 120 4 12 13 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 120 (accept_3_5 47
  52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 120 2 23 26 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 120
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 120 4 11 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 120 (Polychromatic418967fa.accept_16_11_4_8_1_3435 43 52 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 120 2 21 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 120 (accept_3_5 41 52 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 120 4 10 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 52 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 120 2 19 26 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 120 4 9 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 120 (accept_3_5 35 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  120 2 17 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  52 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 120 4 8 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 52 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 52 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 120 2 15 26 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 120 (accept_3_5 29 52 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 120 4 7 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 120 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 52 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 120 2 13 26 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 120 4 6 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 120 (accept_3_5 23 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  120 2 11 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  52 120 (Polychromatic418967fa.accept_16_5_4_8_1_1560 21 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 120 4 5 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 52 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 120 2 9 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 120 (accept_3_5 17 52 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 120 4 4 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 52 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 52 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 120 2 7 26 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 120
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 120 4 3 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 120 (accept_3_5 11 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  120 2 5 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 120 4 2 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 120 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7 52 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 120 2 3 26 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 120 (accept_3_5 5 52 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 120 4 1 13 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 120 (Polychromatic418967fa.accept_16_3_4_8_1_3450 3 52 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 120 2 1 26 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 120
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 52 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 120)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 120 (allA_succ_of_accept 50 51 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 120 3 16 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 47
  51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 120 3 15 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 44 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 51 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 120 3 14 17 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 120 3 13 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 120 3 12 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 51 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 120 3 11 17 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 120 3 10 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 120 3 9 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 51 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 120 3 8 17 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 120 3 7 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 51 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 120 3 6 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 51 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 120 3 5 17 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 120 3 4 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 51 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 120
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 120 3 3 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 51 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 120 3 2 17 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 51 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 120 3 1 17 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 51 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 51 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 120))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 120 (allA_succ_of_accept 49 50 120
  (accept_3_4 49 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 120 2 24 25 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 120 2 23 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 50 120 5 9 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 50 120 2 22 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 50 120 (accept_3_4 43 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50
  120 2 21 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  50 120 (Polychromatic418967fa.accept_13_2_11_3_1_873 41 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 50 120 10 4 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 50 120 (Polychromatic418967fa.accept_17_5_16_1_1_3358 39 50 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 120 2 19 25 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 120 (accept_3_4 37 50 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 120 2 18 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 50 120 5 7 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 50 120 2 17 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 33
  50 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 120 2 16 25 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 120 (accept_3_4 31
  50 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 120 10 3 5 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 120 2 14 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 120 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 50 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 120 2 13 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 50 120 5 5 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 50 120 2 12 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 120 (Polychromatic418967fa.accept_13_10_11_3_1_1518
  23 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 120 2 11 25 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 120
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 120 10 2 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 50 120 (accept_3_4 19 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50
  120 2 9 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  50 120 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 50 120 2 8 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 50 120 5 3 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 50 120 2 7 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 50 120 (accept_3_4 13 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 50 120 2 6 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 50 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 50 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 120 10 1 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 120 (Polychromatic418967fa.accept_23_9_4_5_1_5770 9 50 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 120 2 4 25 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 120 (accept_3_4 7 50 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 120 2 3 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 50 120 5 1 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 50 120 2 2 25 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 120 (Polychromatic418967fa.accept_18_3_14_12_1_1141
  3 50 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 120 2 1 25 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 120 (accept_3_4 1 50
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 120))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 120 (allA_succ_of_accept 48 49 120 (Polychromatic418967fa.accept_11_4_5_10_1_926 48 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 120 (accept_3_5 47 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 49 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 120
  (Polychromatic418967fa.accept_13_6_10_3_1_897 45 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 120 (accept_3_5 44 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 49 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 120 (accept_3_5 41 49 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 120 (Polychromatic418967fa.accept_21_19_7_15_1_2848 40 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 120
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 120 (accept_3_5 38 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 120 (Polychromatic418967fa.accept_16_4_1_8_1_835 36 49 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 120 (accept_3_5 35 49 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 120
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 120 (accept_3_5 32 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 120 (Polychromatic418967fa.accept_16_15_1_8_1_1585 31 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 120 (Polychromatic418967fa.accept_21_9_7_15_1_5769 30 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 120 (accept_3_5 29 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 49 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 120
  (Polychromatic418967fa.accept_14_13_7_8_1_677 27 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 120 (accept_3_5 26 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 49 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 120 (accept_3_5 23 49 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 120 (Polychromatic418967fa.accept_21_1_7_15_1_4259 22 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 120
  (Polychromatic418967fa.accept_18_3_13_12_1_1138 21 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 120 (accept_3_5 20 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 120 (Polychromatic418967fa.accept_19_18_11_6_1_5768 18 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 120 (accept_3_5 17 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 49 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 120
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 120 (accept_3_5 14 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 120 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 120 (Polychromatic418967fa.accept_16_12_1_8_1_5767 12 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 120 (accept_3_5 11 49 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 49 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 120
  (Polychromatic418967fa.accept_16_9_1_8_1_5766 9 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 120 (accept_3_5 8 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  120 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 49 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 120 (accept_3_5 5 49 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 120 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 49 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 120 (Polychromatic418967fa.accept_17_3_15_1_1_3348
  3 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 120 (accept_3_5 2 49
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 120 (Polychromatic418967fa.accept_9_1_4_3_1_201
  1 49 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  120))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 120 (allA_succ_of_accept 47 48 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 48 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 120 2 23 24 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 48 120 3 15 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 48 120 4 11 12 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 120 (Polychromatic418967fa.accept_21_1_6_15_1_5742 43 48 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 120 6 7 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 120 (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 48 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 120 8 5 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 120 3 13 16 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 120 2 19 24 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 120 12 3 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 120 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 48 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 120 2 17 24 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 120 3 11 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 48 120 8 4 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 120 (Polychromatic418967fa.accept_13_5_9_3_1_870 31
  48 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 120 6 5 8 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 120
  (Polychromatic418967fa.accept_21_8_6_15_1_5743 29 48 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 120 4 7 12 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 48 120 3 9 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 48 120 2 13 24 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 120 (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 48 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 120 24 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 120 2 11 24 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 120 3 7 16 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 120 4 5 12 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 120 6 3 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 120 (Polychromatic418967fa.accept_21_17_6_15_1_5765 17 48 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 120 8 2 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 120 3 5 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 120 2 7 24 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 120 (Polychromatic418967fa.accept_17_13_14_1_1_2258 13 48
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 120 12 1 4 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 120
  (Polychromatic418967fa.accept_21_11_6_15_1_5764 11 48 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 120 2 5 24 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 48 120 3 3 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 48 120 8 1 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 120 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 48 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 120 6 1 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 120 4 1 12 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 120 3 1 16 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 120 2 1 24 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 120
  (Polychromatic418967fa.accept_19_1_10_6_1_5726 1 48 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 120)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 120 (allA_succ_of_accept 46 47 120
  (accept_3_4 46 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 47 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 120 (accept_3_4 43 47 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 41
  47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 120 (accept_3_4 40 47
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 120
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 47 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 120 (accept_3_4 37 47 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 120 (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 47 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 120
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 120 (accept_3_4 34 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 120 (accept_3_4 31 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 120 (Polychromatic418967fa.accept_21_9_5_15_1_5741 30 47 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 120
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 120 (accept_3_4 28 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 120 (accept_3_4 25 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 120 (accept_3_4 22 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 120 (Polychromatic418967fa.accept_22_21_3_10_1_5763 21 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 120 (accept_3_4 19 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 47 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 120 (accept_3_4 16 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 120 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 120 (accept_3_4 13 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 120 (Polychromatic418967fa.accept_16_12_15_8_1_4586 12 47 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 120
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 120 (accept_3_4 10 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 120 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 120 (accept_3_4 7 47 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 47 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 120 (accept_3_4 4 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  120 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 47 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 120 (Polychromatic418967fa.accept_17_2_13_1_1_3355 2 47 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 120 (accept_3_4 1 47 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 120))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 120 (allA_succ_of_accept 45
  46 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 46 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 120 2 22 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 46 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 120 2 21 23 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 120 (accept_3_5 41 46 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 120 2 20 23 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 120
  (Polychromatic418967fa.accept_14_11_4_8_1_664 39 46 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 120 2 19 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 120 (Polychromatic418967fa.accept_13_11_7_3_1_894 37 46 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 120 2 18 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 120 (accept_3_5 35 46 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 120 2 17 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 46 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 120 2 16 23 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 46 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 120 2 15 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 46 120 (accept_3_5 29 46 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46
  120 2 14 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  46 120 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 46 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 46 120 2 13 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 46 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 46 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 120 2 12 23 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 120 (accept_3_5 23 46 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 120 2 11 23 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 120
  (Polychromatic418967fa.accept_13_8_7_3_1_430 21 46 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 120 2 10 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 46 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 120 2 9 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 120 (accept_3_5 17 46 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 120 2 8 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 46 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 120 2 7 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 13
  46 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 120 2 6 23 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 120 (accept_3_5 11
  46 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 120 2 5 23 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 120
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 46 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 120 2 4 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 46 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 120 2 3 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 120 (accept_3_5 5 46 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 120 2 2 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 46 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 120 2 1 23 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 120 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1
  46 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  120)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 120 (allA_succ_of_accept 44 45 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 120 (Polychromatic418967fa.accept_16_11_13_8_1_1578 43 45 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 120 3 14 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 120 (Polychromatic418967fa.accept_17_7_11_1_1_4503
  41 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 120 5 8 9 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 45 120 3 13 15 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 120
  (Polychromatic418967fa.accept_21_17_3_15_1_5762 38 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 45 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 120 3 12 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 45 120 5 7 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 120 (Polychromatic418967fa.accept_18_16_9_12_1_1182
  34 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 120 3 11 15 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 120 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 45 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 120 15 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 120 (Polychromatic418967fa.accept_18_11_9_12_1_4427 29 45
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 120
  (Polychromatic418967fa.accept_16_12_13_8_1_2409 28 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 120 3 9 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 45 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 120 5 5 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 120 3 8 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 45 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 120
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 120 3 7 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 45 120 5 4 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 45 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 120 3 6 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 120 (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 45
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 120 15 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 120 (Polychromatic418967fa.accept_13_1_6_3_1_1547 14 45 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 120 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 45 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 120 3 4 15 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 120 5 2 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 45 120 3 3 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 120 (Polychromatic418967fa.accept_17_8_11_1_1_5761 8 45 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 120 (Polychromatic418967fa.accept_17_7_11_1_1_4503 7 45 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 120 3 2 15 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 45 120 5 1 9 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 45 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 120 3 1 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 45 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 120 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 45 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  120))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 120 (allA_succ_of_accept 43 44 120 (accept_3_4 43 44
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 120 2 21 22 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 120 4 10 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 120 (Polychromatic418967fa.accept_16_7_12_8_1_2450 39 44 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 120 2 19 22 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 120 (accept_3_4 37 44 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 120 4 9 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 44 120 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 44 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 120 2 17 22 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 120
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 120 4 8 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 120 (accept_3_4 31 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  120 2 15 22 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 120 4 7 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 44 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 120 2 13 22 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 120 (accept_3_4 25 44 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 120 4 6 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 44 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 120 2 11 22 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 120
  (Polychromatic418967fa.accept_13_8_5_3_1_427 21 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 120 4 5 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 120 (accept_3_4 19 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  120 2 9 22 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 120 4 4 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 44 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 120 2 7 22 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 120 (accept_3_4 13 44 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 120 4 3 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 44 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 120 2 5 22 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 120
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 120 4 2 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 120 (accept_3_4 7 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 120
  2 3 22 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  120 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 44 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 120 4 1 11 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 120 2 1 22 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 120 (accept_3_4 1 44 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 120)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 120 (allA_succ_of_accept 42 43
  120 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 120 (accept_3_5 41 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 120 (Polychromatic418967fa.accept_18_3_7_12_1_1196 39 43 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 120 (accept_3_5 38 43 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 43 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 120
  (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 120 (accept_3_5 35 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 120 (Polychromatic418967fa.accept_19_15_5_6_1_5760 34 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 120 (accept_3_5 32 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 43 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 120
  (Polychromatic418967fa.accept_14_2_1_8_1_650 30 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 120 (accept_3_5 29 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 120 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 120 (accept_3_5 26 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 120 (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 43 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 120
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 120 (accept_3_5 23 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 120 (Polychromatic418967fa.accept_14_7_1_8_1_2873 21 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 120 (accept_3_5 20 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 43 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 120
  (Polychromatic418967fa.accept_19_18_5_6_1_2004 18 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 120 (accept_3_5 17 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 120 (Polychromatic418967fa.accept_14_2_1_8_1_650 16 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 120 (accept_3_5 14 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 43 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 120
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 120 (accept_3_5 11 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 120 (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 120 (accept_3_5 8 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 120 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 43 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 120
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 120 (accept_3_5 5 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  120 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 43 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 120 (Polychromatic418967fa.accept_16_3_11_8_1_830 3 43 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 120 (accept_3_5 2 43 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 43 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 120))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 120
  (allA_succ_of_accept 41 42 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 42 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 120 2 20 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 120 3 13 14 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 120 2 19 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 37
  42 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 120 6 6 7 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 120
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 42 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 120 2 17 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 42 120 3 11 14 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 42 120 2 16 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 42 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 120 6 5 7 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 42 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 120 2 14 21 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 120 3 9 14 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 120 2 13 21 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 120
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 42 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 120 6 4 7 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 42 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 120 2 11 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 120 3 7 14 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 120 2 10 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 19
  42 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 120 6 3 7 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 120
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 42 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 120 2 8 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 120 3 5 14 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 120 2 7 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 42 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 120 6 2 7 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 42 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 120 2 5 21 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 120 3 3 14 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 120 2 4 21 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 120
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 42 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 120 6 1 7 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 120 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 42 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 120 2 2 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 120 3 1 14 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 120 2 1 21 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 42 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  120)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 120 (allA_succ_of_accept 40 41 120 (accept_3_4 40 41 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 120 (Polychromatic418967fa.accept_16_7_9_8_1_829
  39 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 120 (accept_3_4 37 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 120 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 120 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 120 (accept_3_4 34 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 41 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 120
  (Polychromatic418967fa.accept_25_7_16_20_1_5759 32 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 120 (accept_3_4 31 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 120 (accept_3_4 28 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 120 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 41 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 120 (accept_3_4 25 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 120 (accept_3_4 22 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 120 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 41 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 120 (accept_3_4 19 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 120 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 120 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 120 (accept_3_4 16 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 41 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 120
  (Polychromatic418967fa.accept_13_1_2_3_1_911 14 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 120 (accept_3_4 13 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 120 (accept_3_4 10 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 41 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 120
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 120 (accept_3_4 7 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  120 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 41 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 120 (accept_3_4 4 41 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 120 (Polychromatic418967fa.accept_26_3_15_16_1_5758 3 41 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 41
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 120 (accept_3_4 1 41 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 120))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 120
  (allA_succ_of_accept 39 40 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 40 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 120 2 19 20 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 37
  40 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 120 4 9 10 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 40 120 5 7 8 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 40 120 2 17 20 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 120
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 40 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 120 8 4 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 40 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 120 10 3 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 120 (accept_3_5 29 40 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 40 120 4 7 10 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 40 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 40 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 120 2 13 20 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 40 120 5 5 8 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 40 120 8 3 5 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 120 (accept_3_5 23 40 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 120 2 11 20 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 120
  (Polychromatic418967fa.accept_22_21_18_10_1_5757 21 40 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 40 120 20 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 40 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 40 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 120 2 9 20 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 120 (accept_3_5 17 40 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 120 8 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 40 120 5 3 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 40 120 2 7 20 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 40 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 40 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 120 4 3 10 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 120 (accept_3_5 11 40 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 120 10 1 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 120 (Polychromatic418967fa.accept_18_9_4_12_1_3209 9 40 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 120 8 1 5 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 120
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 40 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 40 120 2 3 20 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 40 120 5 1 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 40 120 4 1 10 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 40 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 40 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 120 2 1 20 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 40 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 120))))))))))))))))))))))))))))))))))))))))
  (allB_succ 39 120 (allA_succ_of_accept 38 39 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 39 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 120
  (Polychromatic418967fa.accept_18_1_3_12_1_467 37 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 39 120 3 12 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 39 120 (Polychromatic418967fa.accept_21_14_18_15_1_5756 35 39 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 120 (Polychromatic418967fa.accept_21_13_18_15_1_2837 34 39
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 39 120 3 11 13 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 39 120
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 39 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 120 3 10 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 120 (Polychromatic418967fa.accept_19_10_1_6_1_5755
  29 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 120
  (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 39 120 3 9 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 39 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 39 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 120 (Polychromatic418967fa.accept_16_9_7_8_1_1588 25 39 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 120 3 8 13 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 120
  (Polychromatic418967fa.accept_17_6_5_1_1_5754 23 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 120 (Polychromatic418967fa.accept_19_3_1_6_1_3114 22 39 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 120 3 7 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 120 (Polychromatic418967fa.accept_16_4_7_8_1_5753 20 39 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 39 120 3 6 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 39 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 39 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 120 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 39
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 120 3 5 13 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 120
  (Polychromatic418967fa.accept_18_14_3_12_1_3249 14 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 120 (Polychromatic418967fa.accept_18_13_3_12_1_3207 13 39 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 120 3 4 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 120 (Polychromatic418967fa.accept_19_11_1_6_1_5752 11 39 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 10 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 39 120 3 3 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 39 120 (Polychromatic418967fa.accept_18_8_3_12_1_3247 8 39 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 120 (Polychromatic418967fa.accept_18_7_3_12_1_3241 7 39 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 120 3 2 13 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 120
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 39 120 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 39 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 120 3 1 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 120 (Polychromatic418967fa.accept_18_2_3_12_1_1155 2 39 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 120
  (Polychromatic418967fa.accept_16_1_7_8_1_3422 1 39 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 39 120))))))))))))))))))))))))))))))))))))))) (allB_succ 38 120 (allA_succ_of_accept 37 38 120 (accept_3_4
  37 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38 120 2 18 19 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 38 120
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 38 120 2 17 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 38 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 38 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 120 2 16 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 120 (accept_3_4 31 38 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 120 2 15 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 120 (Polychromatic418967fa.accept_21_8_17_15_1_2834 29 38
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 38 120 2 14 19 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 38 120
  (Polychromatic418967fa.accept_21_6_17_15_1_2833 27 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 38 120 2 13 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 38 120 (accept_3_4 25 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38
  120 2 12 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  38 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 38 120 2 11 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 38 120 (Polychromatic418967fa.accept_18_3_2_12_1_5751 21 38 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 120 2 10 19 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 120 (accept_3_4 19 38 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38 120 2 9 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 38 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 17
  38 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 120 2 8 19 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 120
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 38 120 2 7 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 38 120 (accept_3_4 13 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38
  120 2 6 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  38 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 38 120 2 5 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 38 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 38 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 120 2 4 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 120 (accept_3_4 7 38 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 120 2 3 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 38 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 38 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 120 2 2 19 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 120
  (Polychromatic418967fa.accept_18_3_2_12_1_5751 3 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 38 120 2 1 19 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 38 120 (accept_3_4 1 38 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  120)))))))))))))))))))))))))))))))))))))) (allB_succ 37 120 (allA_succ_of_accept 36 37 120
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 120 (accept_3_5 35 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 37 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 120 (accept_3_5 32 37 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 120
  (Polychromatic418967fa.accept_19_11_18_6_1_3113 30 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 120 (accept_3_5 29 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 120 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 37 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 120 (accept_3_5 26 37 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 37 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 120
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 120 (accept_3_5 23 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 120 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 37 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 120 (accept_3_5 20 37 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 120 (Polychromatic418967fa.accept_16_3_5_8_1_4543 19 37 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 120
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 120 (accept_3_5 17 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 37 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 120 (accept_3_5 14 37 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 120
  (Polychromatic418967fa.accept_16_12_5_8_1_2492 12 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 120 (accept_3_5 11 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 120 (Polychromatic418967fa.accept_17_9_3_1_1_2275 9 37 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 120 (accept_3_5 8 37 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 37 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 120 (accept_3_5 5 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  120 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 37 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 37 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 120 (accept_3_5 2 37 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 120 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 37 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 120))))))))))))))))))))))))))))))))))))) (allB_succ 36 120
  (allA_succ_of_accept 35 36 120 (Polychromatic418967fa.accept_16_3_4_8_1_3450 35 36 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 120 2 17 18 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 120 3 11 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 120 4 8 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 120 (Polychromatic418967fa.accept_16_15_4_8_1_1562
  31 36 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 120 6 5 6 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 120
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 36 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 120 4 7 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 120 3 9 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 120 2 13 18 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 120 (Polychromatic418967fa.accept_16_9_4_8_1_2533 25 36 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 120 12 2 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 120 (Polychromatic418967fa.accept_16_7_4_8_1_2487 23 36 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 120 2 11 18 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 120 3 7 12 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 120 4 5 9 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 120
  (Polychromatic418967fa.accept_13_6_10_3_1_897 19 36 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 120 6 3 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 120 (Polychromatic418967fa.accept_16_1_4_8_1_3434 17 36 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 120 4 4 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 120 3 5 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 120 2 7 18 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 120 (Polychromatic418967fa.accept_16_13_4_8_1_4557 13 36 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 120 12 1 3 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 120
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 36 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 120 2 5 18 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 36 120 3 3 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 36 120 4 2 9 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 120 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 36 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 120 6 1 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 120 (Polychromatic418967fa.accept_16_5_4_8_1_1560 5 36 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 120 4 1 9 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 120 3 1 12 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 120 2 1 18 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 120
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 36 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 120)))))))))))))))))))))))))))))))))))) (allB_succ 35 120 (allA_succ_of_accept 34 35 120 (accept_3_4 34
  35 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 120
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 35 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 35 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 120 (accept_3_4 31 35 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 120 5 6 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 35 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 120 (accept_3_4 28 35 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 120 (Polychromatic418967fa.accept_14_13_7_8_1_677 27 35 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 120
  (Polychromatic418967fa.accept_19_7_16_6_1_4400 26 35 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 120 5 5 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 35 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 35 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 120 (accept_3_4 22 35 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 120 (Polychromatic418967fa.accept_13_8_9_3_1_2213
  21 35 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 120 5 4 7 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 120 (accept_3_4 19
  35 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 120
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 35 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 120 (Polychromatic418967fa.accept_21_17_14_15_1_5750 17 35 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 120 (accept_3_4 16 35 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 120 5 3 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 35 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 120 (accept_3_4 13 35 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 120 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 35 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 120
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 35 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 120 5 2 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 120 (Polychromatic418967fa.accept_18_9_17_12_1_462 9 35 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 120 (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 35 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 120 (accept_3_4 7 35 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 6
  35 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 120 5 1 7 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 120 (accept_3_4 4 35
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 120
  (Polychromatic418967fa.accept_19_3_16_6_1_1987 3 35 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 120 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 35 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 120 (accept_3_4 1 35 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 120))))))))))))))))))))))))))))))))))) (allB_succ 34 120 (allA_succ_of_accept 33 34 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 34 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 120 2 16 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 34 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 120 2 15 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 120 (accept_3_5 29 34 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 120 2 14 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 120 (Polychromatic418967fa.accept_18_9_16_12_1_1143 27 34
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 120 2 13 17 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 120
  (Polychromatic418967fa.accept_29_25_5_4_1_5749 25 34 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 120 2 12 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 120 (accept_3_5 23 34 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  120 2 11 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 120 (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 34 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 120 2 10 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 34 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 120 2 9 17 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 120 (accept_3_5 17 34 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 120 2 8 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 34 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 120 2 7 17 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 120
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 34 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 120 2 6 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 120 (accept_3_5 11 34 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  120 2 5 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 34 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 120 2 4 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 120 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 34 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 120 2 3 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 120 (accept_3_5 5 34 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 120 2 2 17 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 120 (Polychromatic418967fa.accept_27_3_7_12_1_5748 3 34 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 120 2 1 17 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 120
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 34 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 120)))))))))))))))))))))))))))))))))) (allB_succ 33 120 (allA_succ_of_accept 32 33 120
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 33 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 120 3 10 11 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  33 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 33 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 120 3 9 11 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 33 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 120 3 8 11 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 33 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 33 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 120 3 7 11 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 33 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 120 3 6 11 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 33 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 33 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 120 3 5 11 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 33 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 120 3 4 11 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 33 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 33 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 120 3 3 11 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 33 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 33 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 120 3 2 11 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 33 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 33 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 120 3 1 11 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 33 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 33 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 120))))))))))))))))))))))))))))))))) (allB_succ 32 120 (allA_succ_of_accept 31 32 120 (accept_3_4 31 32
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 120 2 15 16 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 32 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 120 4 7 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 120 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 32 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 120 2 13 16 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 120 (accept_3_4 25 32 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 120 8 3 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 32 120 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 32 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 120 2 11 16 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 120
  (Polychromatic418967fa.accept_18_3_14_12_1_1141 21 32 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 120 4 5 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 120 (accept_3_4 19 32 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  120 2 9 16 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 120 8 2 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 32 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 120 2 7 16 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 120 (accept_3_4 13 32 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 120 4 3 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 32 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 120 2 5 16 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 120
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 32 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 120 8 1 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 120 (accept_3_4 7 32 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 120
  2 3 16 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  120 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 120 4 1 8 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 120 2 1 16 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 120 (accept_3_4 1 32 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 120)))))))))))))))))))))))))))))))) (allB_succ 31 120 (allA_succ_of_accept 30 31 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 120 (accept_3_5 29 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 120 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 31 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 120 (accept_3_5 26 31 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 120 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 31 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 120
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 120 (accept_3_5 23 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 120 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 120 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 31 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 120 (accept_3_5 20 31 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 120 (accept_3_5 17 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 120 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 31 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 120 (accept_3_5 14 31 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 120 (Polychromatic418967fa.accept_17_13_14_1_1_2258 13 31 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 120
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 120 (accept_3_5 11 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 31 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 120 (accept_3_5 8 31 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 31 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 120
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 120 (accept_3_5 5 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  120 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 120 (Polychromatic418967fa.accept_18_3_13_12_1_1138 3 31 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 120 (accept_3_5 2 31 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 31 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 120))))))))))))))))))))))))))))))) (allB_succ 30 120
  (allA_succ_of_accept 29 30 120 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 30 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 120 2 14 15 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 120 3 9 10 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 120 2 13 15 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 120 5 5 6 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 120 6 4 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 120 (Polychromatic418967fa.accept_21_2_9_15_1_5747
  23 30 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 120 2 11 15 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 120 3 7 10 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 120 10 2 3 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 120
  (Polychromatic418967fa.accept_17_2_13_1_1_3355 19 30 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 120 6 3 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 120 2 8 15 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 120 15 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 120 2 7 15 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 30 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 120 6 2 5 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 120
  (Polychromatic418967fa.accept_21_11_9_15_1_5746 11 30 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 120 10 1 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 30 120 3 3 10 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 30 120 2 4 15 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 120 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 30 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 120 6 1 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 120 5 1 6 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 120 2 2 15 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 30 120 3 1 10 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 30 120 2 1 15 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 120 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 30 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 120)))))))))))))))))))))))))))))) (allB_succ
  29 120 (allA_succ_of_accept 28 29 120 (accept_3_4 28 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 120 (Polychromatic418967fa.accept_16_11_13_8_1_1578 27 29 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 29 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 120 (accept_3_4 25 29 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 24
  29 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 120 (accept_3_4 22 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 120 (Polychromatic418967fa.accept_14_7_1_8_1_2873 21 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 120 (Polychromatic418967fa.accept_16_4_13_8_1_3424 20 29 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 120 (accept_3_4 19 29 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 120 (Polychromatic418967fa.accept_21_18_8_15_1_5745 18 29
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 120
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 120 (accept_3_4 16 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 120 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 29 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 120 (accept_3_4 13 29 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 120 (Polychromatic418967fa.accept_16_12_13_8_1_2409 12 29 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 120
  (Polychromatic418967fa.accept_16_11_13_8_1_1578 11 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 120 (accept_3_4 10 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 120 (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 29 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 120 (accept_3_4 7 29 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 29 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 120
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 120 (accept_3_4 4 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  120 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 29 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 29 120 (Polychromatic418967fa.accept_14_2_1_8_1_650 2 29 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 120 (accept_3_4 1 29 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 29 120))))))))))))))))))))))))))))) (allB_succ 28 120 (allA_succ_of_accept 27 28 120
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 28 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 120 2 13 14 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 28 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 120 4 6 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 120 (accept_3_5 23 28 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 120 2 11 14 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 28 120 (Polychromatic418967fa.accept_16_5_12_8_1_2521 21 28 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 120 4 5 7 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 120
  (Polychromatic418967fa.accept_16_3_12_8_1_808 19 28 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 120 2 9 14 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 120 (accept_3_5 17 28 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  120 4 4 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 28 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 120 2 7 14 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 120 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 28 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 120 4 3 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 120 (accept_3_5 11 28 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 120 2 5 14 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 28 120 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 28 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 120 4 2 7 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 120
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 28 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 120 2 3 14 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 120 (accept_3_5 5 28 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 120
  4 1 7 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 120
  (Polychromatic418967fa.accept_16_3_12_8_1_808 3 28 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 120 2 1 14 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 120 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 28 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 120)))))))))))))))))))))))))))) (allB_succ 27 120 (allA_succ_of_accept 26
  27 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 27 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 120 (Polychromatic418967fa.accept_21_4_6_15_1_5744 25 27 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 120 3 8 9 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 27 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 120 (Polychromatic418967fa.accept_18_4_9_12_1_1175 22 27 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 120 3 7 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 120 (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 27 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 120 3 6 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 120 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 27 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 27 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 120 3 5 9 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 120
  (Polychromatic418967fa.accept_17_14_10_1_1_4523 14 27 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 120 (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 27 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 120 3 4 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 120 (Polychromatic418967fa.accept_13_11_1_3_1_910 11 27 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 120
  (Polychromatic418967fa.accept_18_10_9_12_1_3259 10 27 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 120 3 3 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 120 (Polychromatic418967fa.accept_21_8_6_15_1_5743 8 27 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 120 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 27 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 120 3 2 9 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 120
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 27 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 120 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 27 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 120 3 1 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 27 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 120
  (Polychromatic418967fa.accept_21_1_6_15_1_5742 1 27 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 120))))))))))))))))))))))))))) (allB_succ 26 120 (allA_succ_of_accept 25 26 120 (accept_3_4 25 26 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 120 2 12 13 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 120
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 26 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 120 2 11 13 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 26 120 (Polychromatic418967fa.accept_18_3_8_12_1_3283 21 26 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 120 2 10 13 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 120 (accept_3_4 19 26 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 120 2 9 13 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 120 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 26 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 120 2 8 13 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 120
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 26 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 120 2 7 13 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 120 (accept_3_4 13 26 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  120 2 6 13 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 26 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 120 2 5 13 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 120 (Polychromatic418967fa.accept_21_9_5_15_1_5741 9 26 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 120 2 4 13 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 120 (accept_3_4 7 26 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 120 2 3 13 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 26 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 120 2 2 13 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 26 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 120 2 1 13 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 120 (accept_3_4 1 26 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  120)))))))))))))))))))))))))) (allB_succ 25 120 (allA_succ_of_accept 24 25 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 120 (accept_3_5 23 25 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 25 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 120 (Polychromatic418967fa.accept_17_4_8_1_1_5740 21 25 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 120 5 4 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 19
  25 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 120
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 25 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 120 (accept_3_5 17 25 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 120 (Polychromatic418967fa.accept_22_16_3_10_1_5739 16 25 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 25 120 5 3 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 25 120 (accept_3_5 14 25 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 25 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 25 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 120 (accept_3_5 11 25 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 120 5 2 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 120 (Polychromatic418967fa.accept_13_9_12_3_1_907 9
  25 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 120 (accept_3_5 8 25 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 120 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  7 25 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 120
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 25 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 120 5 1 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 25 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 25 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 120 (accept_3_5 2 25 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 25
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 120))))))))))))))))))))))))) (allB_succ
  24 120 (allA_succ_of_accept 23 24 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 120 2 11 12 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 120 3 7 8 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 120 4 5 6 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 120
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 120 6 3 4 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 120 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 24 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 120 8 2 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 24 120 3 5 8 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 24 120 2 7 12 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 24 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 120 12 1 2 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 24 120 2 5 12 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 24 120 3 3 8 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 24 120 8 1 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 24 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 120 6 1 4 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 120 4 1 6 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 120 3 1 8 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 120 2 1 12 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 120
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 24 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 120)))))))))))))))))))))))) (allB_succ 23 120 (allA_succ_of_accept 22 23 120 (accept_3_4 22 23 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 120 (Polychromatic418967fa.accept_19_2_4_6_1_5738
  21 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 120
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 120 (accept_3_4 19 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 120 (Polychromatic418967fa.accept_21_18_2_15_1_5737 18 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 23 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 120 (accept_3_4 16 23 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 120 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 23 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 120
  (Polychromatic418967fa.accept_22_14_1_10_1_5736 14 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 120 (accept_3_4 13 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 120 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 23 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 120 (accept_3_4 10 23 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 120 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 23 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 120
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 120 (accept_3_4 7 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  120 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 23 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 120 (Polychromatic418967fa.accept_17_5_6_1_1_5735 5 23 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 120 (accept_3_4 4 23 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 120 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 23 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 23
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 120 (accept_3_4 1 23 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 120))))))))))))))))))))))) (allB_succ 22 120
  (allA_succ_of_accept 21 22 120 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 22 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 120 2 10 11 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 19
  22 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 120 2 9 11 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 120 (accept_3_5 17
  22 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 120 2 8 11 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 22 120
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 22 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 22 120 2 7 11 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 22 120 (Polychromatic418967fa.accept_25_13_22_20_1_5734 13 22 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 120 2 6 11 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 120 (accept_3_5 11 22 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 22 120 2 5 11 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 22 120 (Polychromatic418967fa.accept_18_9_4_12_1_3209 9 22 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 120 2 4 11 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 22
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 120 2 3 11 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 120 (accept_3_5 5 22
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 120 2 2 11 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22 120
  (Polychromatic418967fa.accept_21_3_1_15_1_4287 3 22 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 120 2 1 11 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 22 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 120)))))))))))))))))))))) (allB_succ 21 120 (allA_succ_of_accept 20 21
  120 (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 21 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 21 120 (Polychromatic418967fa.accept_16_3_5_8_1_4543 19 21 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 120 3 6 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 120
  (Polychromatic418967fa.accept_22_17_21_10_1_5733 17 21 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 120 (Polychromatic418967fa.accept_23_16_21_5_1_5732 16 21 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 120 3 5 7 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 120
  (Polychromatic418967fa.accept_17_14_4_1_1_3341 14 21 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 120 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 21 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 120 3 4 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 120 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 21 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 120
  (Polychromatic418967fa.accept_19_10_2_6_1_5731 10 21 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 21 120 3 3 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 21 120 (Polychromatic418967fa.accept_17_8_4_1_1_5730 8 21 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 120 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 21 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 120 3 2 7 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 120
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 21 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 120 (Polychromatic418967fa.accept_16_4_5_8_1_2425 4 21 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 120 3 1 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 120 (Polychromatic418967fa.accept_18_2_3_12_1_1155 2 21 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 120
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 1 21 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 120))))))))))))))))))))) (allB_succ 20 120 (allA_succ_of_accept 19 20 120 (accept_3_4 19 20 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 120 2 9 10 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 20 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 20 120 4 4 5 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 20 120 5 3 4 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 20 120 2 7 10 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 120 (accept_3_4 13 20 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 120 4 3 5 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 120 (Polychromatic418967fa.accept_13_11_7_3_1_894
  11 20 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 120 10 1 2 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 120
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 120 4 2 5 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 120 (accept_3_4 7 20 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 120
  2 3 10 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 20 120 5
  1 4 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 20 120 4 1
  5 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 20 120
  (Polychromatic418967fa.accept_16_3_4_8_1_3450 3 20 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 20 120 2 1 10 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 20 120 (accept_3_4 1 20 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  120)))))))))))))))))))) (allB_succ 19 120 (allA_succ_of_accept 18 19 120 (Polychromatic418967fa.accept_7_4_5_1_1_418
  18 19 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 120 (accept_3_5 17
  19 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 120
  (Polychromatic418967fa.accept_9_7_1_3_1_443 16 19 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 19 120 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 19 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 120 (accept_3_5 14 19 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 19 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 19 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 120 (Polychromatic418967fa.accept_16_12_3_8_1_5729
  12 19 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 120 (accept_3_5 11
  19 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 19 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 19 120 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 19 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 120 (accept_3_5 8 19 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 19 120 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 19 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 120 (Polychromatic418967fa.accept_7_6_5_1_1_416 6
  19 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 120 (accept_3_5 5 19 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 4
  19 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 120 (accept_3_5 2 19 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19
  120 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 19 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 19 120))))))))))))))))))) (allB_succ 18 120 (allA_succ_of_accept 17 18 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 120 2 8 9 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 18 120 3 5 6 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 18 120 2 7 9 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 120 (Polychromatic418967fa.accept_21_13_18_15_1_2837 13 18 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 120 6 2 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 120 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 18 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 120 2 5 9 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 18 120 3 3 6 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 18 120 2 4 9 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 120
  (Polychromatic418967fa.accept_19_7_18_6_1_3095 7 18 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 120 6 1 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 120 2 2 9 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 120 3 1 6 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 120 2 1 9 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 120 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 18 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 120)))))))))))))))))) (allB_succ 17 120
  (allA_succ_of_accept 16 17 120 (accept_3_4 16 17 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 17 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 17 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 120 (accept_3_4 13 17 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 120 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 120
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 17 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 120 (accept_3_4 10 17 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 17 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 120 (Polychromatic418967fa.accept_19_8_17_6_1_5728 8 17 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 120 (accept_3_4 7 17 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 120 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 17 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 120
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 120 (accept_3_4 4 17 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  120 (Polychromatic418967fa.accept_19_3_17_6_1_1991 3 17 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 17 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 120 (accept_3_4 1 17 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 120))))))))))))))))) (allB_succ 16 120 (allA_succ_of_accept 15 16 120
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 16 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 120 2 7 8 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 120 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 120 4 3 4 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 120 (accept_3_5 11 16 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 120 2 5 8 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 120 (Polychromatic418967fa.accept_18_9_16_12_1_1143 9 16 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 120 8 1 2 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 120 (Polychromatic418967fa.accept_19_7_16_6_1_4400 7
  16 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 120 2 3 8 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 120 (accept_3_5 5 16
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 120 4 1 4 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 120
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 16 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 120 2 1 8 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 16 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 120)))))))))))))))) (allB_succ 15 120 (allA_succ_of_accept 14 15 120
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 15 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 15 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 120 3 4 5 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 120 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 15 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 120 5 2 3 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 15 120 3 3 5 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 120
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 15 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 120 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 15 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 120 3 2 5 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 120 5 1 3 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 120 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 15 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 120 3 1 5 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 120
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 15 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 15 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 120))))))))))))))) (allB_succ 14 120 (allA_succ_of_accept 13 14 120
  (accept_3_4 13 14 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 120 2 6 7 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 120
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 14 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 120 2 5 7 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 120 (Polychromatic418967fa.accept_19_9_14_6_1_2014 9 14 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 120 2 4 7 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 120 (accept_3_4 7 14 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 120 2 3 7 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 120 (Polychromatic418967fa.accept_13_5_1_3_1_878 5 14 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 120 2 2 7 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 120 (Polychromatic418967fa.accept_18_3_14_12_1_1141
  3 14 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 120 2 1 7 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 120 (accept_3_4 1 14
  120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 120)))))))))))))) (allB_succ 13 120 (allA_succ_of_accept 12
  13 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 120 (accept_3_5 11 13 120 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 13 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 120 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 120 (accept_3_5 8 13 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 120 (Polychromatic418967fa.accept_9_7_4_3_1_204 7
  13 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 120
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 13 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 120 (accept_3_5 5 13 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  120 (Polychromatic418967fa.accept_16_4_13_8_1_3424 4 13 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 120 (Polychromatic418967fa.accept_16_3_13_8_1_1594 3 13 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 120 (accept_3_5 2 13 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 13 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 120))))))))))))) (allB_succ 12 120
  (allA_succ_of_accept 11 12 120 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 120 2 5 6 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 12 120 3 3 4 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 12 120 4 2 3 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 120 (Polychromatic418967fa.accept_16_7_12_8_1_2450 7 12 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 120 6 1 2 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 120
  (Polychromatic418967fa.accept_16_5_12_8_1_2521 5 12 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 120 4 1 3 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 12 120 3 1 4 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 12 120 2 1 6 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 120 (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 12 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 120)))))))))))) (allB_succ 11 120 (allA_succ_of_accept 10 11 120
  (accept_3_4 10 11 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 120
  (Polychromatic418967fa.accept_18_9_11_12_1_5727 9 11 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 120 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 11 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 120 (accept_3_4 7 11 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 120 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 11 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 120 (Polychromatic418967fa.accept_7_5_4_1_1_412 5
  11 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 120 (accept_3_4 4 11 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 120 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 11
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 120
  (Polychromatic418967fa.accept_13_2_11_3_1_873 2 11 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 120 (accept_3_4 1 11 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  120))))))))))) (allB_succ 10 120 (allA_succ_of_accept 9 10 120 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 10 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 120 2 4 5 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 120
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 10 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 120 2 3 5 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 10 120 5 1 2 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 10 120 2 2 5 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 10 120 (Polychromatic418967fa.accept_21_3_10_15_1_4266 3 10 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 120 2 1 5 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 120 (Polychromatic418967fa.accept_19_1_10_6_1_5726 1 10 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 120)))))))))) (allB_succ 9 120
  (allA_succ_of_accept 8 9 120 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 9 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 120 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 9 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 120 3 2 3 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 120
  (Polychromatic418967fa.accept_13_5_9_3_1_870 5 9 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 120 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 9 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 120 3 1 3 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 120 (Polychromatic418967fa.accept_13_2_9_3_1_2212 2 9 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 120
  (Polychromatic418967fa.accept_11_1_9_10_1_184 1 9 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 120))))))))) (allB_succ 8 120 (allA_succ_of_accept 7 8 120 (accept_3_4 7 8 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 120 2 3 4 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 8 120 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 8 120 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 120 4 1 2 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 120
  (Polychromatic418967fa.accept_18_3_8_12_1_3283 3 8 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 120 2 1 4 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 120 (accept_3_4 1 8 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 120))))))))
  (allB_succ 7 120 (allA_succ_of_accept 6 7 120 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 7 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 120 (accept_3_5 5 7 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 7 120 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 7 120 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 120 (Polychromatic418967fa.accept_11_3_7_10_1_180 3
  7 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 120 (accept_3_5 2 7 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 120 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 7
  120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 120))))))) (allB_succ 6 120
  (allA_succ_of_accept 5 6 120 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 120 2 2 3 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 6 120 3 1 2 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 6 120 2 1 3 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 120 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 6 120
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 120)))))) (allB_succ 5 120
  (allA_succ_of_accept 4 5 120 (accept_3_4 4 5 120 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 120
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 5 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 120 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 5 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 120 (accept_3_4 1 5 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 120))))) (allB_succ 4 120 (allA_succ_of_accept 3 4 120
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 4 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 120 2 1 2 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 120 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 4 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 4 120)))) (allB_succ 3 120 (allA_succ_of_accept 2 3 120
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 3 120 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 120 (Polychromatic418967fa.accept_18_1_3_12_1_467 1 3 120 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 120))) (allB_succ 2 120 (allA_succ_of_accept 1 2 120 (accept_3_4 1 2 120
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 120)) (allB_two
  120))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


