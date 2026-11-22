-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch104
-- name    : Polychromatic418967fa_Branch104
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:23.860172+00:00
-- url     : https://prove2.me/theorems/403c4c60-0123-4c33-b6e6-e88ada3b0f83
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

def Polychromatic418967fa.branch_104 : allB 104 104 :=
  allB_succ' 2 103 104 (Eq.refl Bool.true) (allA_of_3_0 2 103 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  102 104 (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 104 2 1 51 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 104 (accept_3_2 1 102 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 102 104))) (allB_succ' 4 101 104 (Eq.refl Bool.true) (allA_succ_of_accept 3 101 104
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 101 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 101 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 104 (accept_3_2 1 101 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 101 104)))) (allB_succ' 5 100 104 (Eq.refl Bool.true) (allA_of_3_0 5 100 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 99 104 (Eq.refl Bool.true) (allA_succ_of_accept 5 99 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 104 (accept_3_2 4 99 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  104 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 99 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 99 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 104 (accept_3_2 1 99 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 104)))))) (allB_succ' 7 98 104 (Eq.refl Bool.true) (allA_succ_of_gcd 6 98 104 2 3 49 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98 104
  (Polychromatic418967fa.accept_12_5_2_8_1_172 5 98 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 98 104 2 2 49 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 98 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 98 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 104 2 1 49 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 104 (accept_3_2 1 98 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 104))))))) (allB_succ' 8 97 104 (Eq.refl Bool.true) (allA_of_3_0 8 97 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 9 96 104 (Eq.refl Bool.true) (allA_succ_of_gcd 8 96 104 8 1 12 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 104 (accept_3_2 7 96 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 104 2 3 48 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 104 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 96
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 104 4 1 24 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 104
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 104 2 1 48 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 104 (accept_3_2 1 96 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 104)))))))))
  (allB_succ' 10 95 104 (Eq.refl Bool.true) (allA_succ_of_accept 9 95 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  95 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 104
  (Polychromatic418967fa.accept_15_8_5_14_1_986 8 95 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 104 (accept_3_2 7 95 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  104 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 95 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 104 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 95 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 104 (accept_3_2 4 95 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  95 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 104 (accept_3_2 1 95 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 104)))))))))) (allB_succ' 11 94 104 (Eq.refl Bool.true)
  (allA_of_3_0 11 94 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 93 104 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 104 (accept_3_2 10 93 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 104 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 93 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 104 (accept_3_2 7 93 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 6
  93 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 104 (accept_3_2 4 93 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  104 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 104 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 93 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 104 (accept_3_2 1 93 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 104)))))))))))) (allB_succ' 13 92 104 (Eq.refl Bool.true) (allA_succ_of_gcd 12 92 104 4 3 23
  26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 104
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 11 92 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 92 104 2 5 46 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 92 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 104 4 2 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 104 (accept_3_2 7 92 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 92 104 2 3 46 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 92 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 104 4 1 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 92
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 104 2 1 46 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 104 (accept_3_2 1 92
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 104))))))))))))) (allB_succ' 14 91 104 (Eq.refl Bool.true)
  (allA_of_3_0 14 91 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 90 104 (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 90 104 2 7 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 104 (accept_3_2 13 90 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90
  104 2 6 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  90 104 (Polychromatic418967fa.accept_19_11_14_9_1_4599 11 90 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 104 2 5 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 104 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 90 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 104 2 4 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 104 (accept_3_2 7 90 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 104 2 3 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 90 104 (Polychromatic418967fa.accept_19_5_14_9_1_4554 5 90 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 104 2 2 45 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 104
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 90 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 104 2 1 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 104 (accept_3_2 1 90 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  104))))))))))))))) (allB_succ' 16 89 104 (Eq.refl Bool.true) (allA_succ_of_accept 15 89 104
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 89 104 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 89 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 104 (accept_3_2 13 89 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 89 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 104 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  89 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 104 (accept_3_2 10 89
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 104 (Polychromatic418967fa.accept_6_3_5_2_1_12
  9 89 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 104
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 104 (accept_3_2 7 89 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  104 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 89 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 104 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 89 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 104 (accept_3_2 4 89 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 104 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  89 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 104 (accept_3_2 1 89 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 104)))))))))))))))) (allB_succ' 17 88 104 (Eq.refl Bool.true)
  (allA_of_3_0 17 88 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 87 104 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 87 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 104 (accept_3_2 16 87 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 104 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 87 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 104
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 14 87 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 104 (accept_3_2 13 87 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 104 (accept_3_2 10 87 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 104
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 87 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 104 (accept_3_2 7 87 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  104 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 87 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 87 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 104 (accept_3_2 4 87 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 104
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 104 (accept_3_2 1 87 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  104)))))))))))))))))) (allB_succ' 19 86 104 (Eq.refl Bool.true) (allA_succ_of_gcd 18 86 104 2 9 43 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 86 104
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 86 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 86 104 2 8 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 86 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 86 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 104 2 7 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 104 (accept_3_2 13 86 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 86 104 2 6 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 86 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 86 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 86 104 2 5 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 86 104 (Polychromatic418967fa.accept_21_9_2_20_1_857 9
  86 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 104 2 4 43 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 104 (accept_3_2 7 86
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 104 2 3 43 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 86 104
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 86 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 86 104 2 2 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 86 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 104 2 1 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 104 (accept_3_2 1 86 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 104))))))))))))))))))) (allB_succ' 20 85 104 (Eq.refl Bool.true) (allA_of_3_0 20 85 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 84 104 (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 104 4 5 21
  26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 104
  (accept_3_2 19 84 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 104 2 9 42 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 104
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 84 104 4 4 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 84 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 104 2 7 42 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 104 (accept_3_2 13 84 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 84 104 4 3 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 84 104 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 104 2 5 42 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 104 (Polychromatic418967fa.accept_11_9_7_5_1_749 9
  84 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 104 4 2 21 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 104 (accept_3_2 7 84
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 104 2 3 42 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 104
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 84 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 104 4 1 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 104 (Polychromatic418967fa.accept_16_3_4_8_1_3450 3 84 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 104 2 1 42 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 104 (accept_3_2 1 84 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 104))))))))))))))))))))) (allB_succ' 22 83 104 (Eq.refl Bool.true) (allA_succ_of_accept 21 83
  104 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 83 104 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 83 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 104 (accept_3_2 19 83 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 83 104 (Polychromatic418967fa.accept_22_18_17_16_1_4598 18 83 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 104
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 104 (accept_3_2 16 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 104 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 83 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 104 (accept_3_2 13 83 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 104
  (Polychromatic418967fa.accept_16_11_3_8_1_4597 11 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 104 (accept_3_2 10 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 104 (accept_3_2 7 83 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 104
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 5 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 104 (accept_3_2 4 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 104 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 83 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 104 (accept_3_2 1 83 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 104)))))))))))))))))))))) (allB_succ' 23 82 104 (Eq.refl Bool.true) (allA_of_3_0 23 82 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 81 104 (Eq.refl Bool.true) (allA_succ_of_accept 23 81 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 104 (accept_3_2 22 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 104 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 104 (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 81 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 104 (accept_3_2 19 81 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 104 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 104 (accept_3_2 16 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 104 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 104 (Polychromatic418967fa.accept_19_14_5_9_1_4596 14 81 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 104 (accept_3_2 13 81 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 104 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 104 (accept_3_2 10 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 104 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 81 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 104 (accept_3_2 7 81 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 104 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 81 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 104 (accept_3_2 4 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  104 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 81 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 104 (accept_3_2 1 81 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 104)))))))))))))))))))))))) (allB_succ' 25 80 104 (Eq.refl Bool.true) (allA_succ_of_gcd 24 80
  104 8 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  80 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 80 104 2 11 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 80 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 80 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 104 4 5 20 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 104 (accept_3_2 19 80 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 104 2 9 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 80 104 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 80 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 104 8 2 10 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 104
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 80 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 80 104 2 7 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 104 (accept_3_2 13 80 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  104 4 3 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 104 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 104 2 5 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 104 8 1 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 104 (accept_3_2 7 80 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 104 2 3 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 80 104 (Polychromatic418967fa.accept_18_5_8_14_1_1282 5 80 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 104 4 1 20 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 104
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 104 2 1 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 104 (accept_3_2 1 80 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  104))))))))))))))))))))))))) (allB_succ' 26 79 104 (Eq.refl Bool.true) (allA_of_3_0 26 79 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 78 104 (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 104 26 1 3 4 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 104 (accept_3_2 25
  78 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 104 2 12 39 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 104
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 104 2 11 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 78 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 104 2 10 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 104 (accept_3_2 19 78 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 104 2 9 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 78 104 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 78 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 104 2 8 39 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 104
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 78 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 104 2 7 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 13 78 104 13 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 78 104 2 6 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 104 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 104 2 5 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 104 2 4 39 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 104 (accept_3_2 7 78 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 104 2 3 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 104 2 2 39 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 104
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 78 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 104 2 1 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 104 (accept_3_2 1 78 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  104))))))))))))))))))))))))))) (allB_succ' 28 77 104 (Eq.refl Bool.true) (allA_succ_of_accept 27 77 104
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 77 104 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 104 (accept_3_2 25 77 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 77 104 (Polychromatic418967fa.accept_17_7_9_2_1_629 24 77 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 104 (Polychromatic418967fa.accept_10_3_7_4_1_584
  23 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 104 (accept_3_2 22
  77 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 104
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 77 104 (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 77 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 104 (accept_3_2 19 77 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 77 104 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 77 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 104
  (Polychromatic418967fa.accept_19_17_1_9_1_4595 17 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 104 (accept_3_2 16 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 104 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 104 (accept_3_2 13 77 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 104 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 77 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 104
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 104 (accept_3_2 10 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 104 (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 77 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 104 (accept_3_2 7 77 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 104 (Polychromatic418967fa.accept_21_6_14_20_1_4594 6 77 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 104
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 104 (accept_3_2 4 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 104 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 77 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 104 (accept_3_2 1 77 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 104)))))))))))))))))))))))))))) (allB_succ' 29 76 104 (Eq.refl Bool.true) (allA_of_3_0 29 76
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 75 104 (Eq.refl Bool.true) (allA_succ_of_accept 29 75 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 104 (accept_3_2 28 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  75 104 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 75 104 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 75 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 104 (accept_3_2 25 75 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 104 (accept_3_2 22 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  75 104 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 75 104 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 75 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 104 (accept_3_2 19 75 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 104 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 104 (accept_3_2 16 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  75 104 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 75 104 (Polychromatic418967fa.accept_27_14_21_23_1_4593 14 75 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 104 (accept_3_2 13 75 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 104 (Polychromatic418967fa.accept_16_12_11_8_1_832 12 75
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 104 (accept_3_2 10 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 104 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 104 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 104 (accept_3_2 7 75 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 104 (accept_3_2 4 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  104 (Polychromatic418967fa.accept_16_3_11_8_1_830 3 75 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 75 104 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 75 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 104 (accept_3_2 1 75 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 75 104)))))))))))))))))))))))))))))) (allB_succ' 31 74 104 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 74 104 2 15 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 74 104 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 74 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 104 2 14 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 104 (Polychromatic418967fa.accept_19_8_17_9_1_4542
  27 74 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 104 2 13 37 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 104 (accept_3_2 25
  74 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 104 2 12 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 104
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 74 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 74 104 2 11 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 74 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 74 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 104 2 10 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 104 (accept_3_2 19 74 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 104 2 9 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 74 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 74 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 104 2 8 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 104
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 74 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 104 2 7 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 104 (accept_3_2 13 74 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  104 2 6 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 104 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 104 2 5 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 74 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 104 2 4 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 104 (accept_3_2 7 74 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 104 2 3 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 104 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 74 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 104 2 2 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 104
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 74 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 104 2 1 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 104 (accept_3_2 1 74 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  104))))))))))))))))))))))))))))))) (allB_succ' 32 73 104 (Eq.refl Bool.true) (allA_of_3_0 32 73 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 72 104 (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 104 8 4 9 13
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 104
  (accept_3_2 31 72 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 104 2 15 36 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 104
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 104 4 7 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 72 104 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 72 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 104 2 13 36 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 104 (accept_3_2 25 72 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 104 8 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 72 104 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 72 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 104 2 11 36 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 104
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 72 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 104 4 5 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 104 (accept_3_2 19 72 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  104 2 9 36 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 104 8 2 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 104 2 7 36 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 104 (accept_3_2 13 72 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 104 4 3 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 72 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 104 2 5 36 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 104
  (Polychromatic418967fa.accept_15_9_12_14_1_963 9 72 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 104 8 1 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 104 (accept_3_2 7 72 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 104
  2 3 36 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  104 (Polychromatic418967fa.accept_19_5_15_9_1_4592 5 72 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 104 4 1 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 104 2 1 36 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 104 (accept_3_2 1 72 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 104))))))))))))))))))))))))))))))))) (allB_succ' 34 71 104 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 71 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 104 (Polychromatic418967fa.accept_21_11_8_20_1_4591 32 71
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 104 (accept_3_2 31 71 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 30
  71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 104
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 104 (accept_3_2 28 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 71 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 104 (accept_3_2 25 71 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 104 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 71 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 104
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 104 (accept_3_2 22 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 104 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 104 (accept_3_2 19 71 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 104 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 71 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 104
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 104 (accept_3_2 16 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 104 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 104 (accept_3_2 13 71 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 104
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 104 (accept_3_2 10 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 104 (Polychromatic418967fa.accept_19_8_14_9_1_4590 8 71 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 104 (accept_3_2 7 71 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 104 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 71 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 104
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 104 (accept_3_2 4 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 71 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 104 (accept_3_2 1 71 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 104)))))))))))))))))))))))))))))))))) (allB_succ' 35 70 104 (Eq.refl Bool.true) (allA_of_3_0
  35 70 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 69 104 (Eq.refl Bool.true) (allA_succ_of_accept 35
  69 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 69 104 (accept_3_2 34 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 69 104 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 69 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 104 (Polychromatic418967fa.accept_21_11_6_20_1_4589 32 69
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 104 (accept_3_2 31 69 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 30
  69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 104 (accept_3_2 28 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 104 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 104 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 69 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 104 (accept_3_2 25 69 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 104 (Polychromatic418967fa.accept_19_5_12_9_1_4588 24 69 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 104 (accept_3_2 22 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 104 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 69 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 104 (accept_3_2 19 69 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 104 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 69 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 104 (accept_3_2 16 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 104 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 104 (Polychromatic418967fa.accept_19_14_12_9_1_4587 14 69 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 104 (accept_3_2 13 69 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 104 (accept_3_2 10 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 104 (Polychromatic418967fa.accept_21_9_6_20_1_1903 9 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 104 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 69 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 104 (accept_3_2 7 69 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 104 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 104 (accept_3_2 4 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  104 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 69 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 104 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 69 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 104 (accept_3_2 1 69 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 104)))))))))))))))))))))))))))))))))))) (allB_succ' 37 68 104 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 68 104 4 9 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 68 104 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 68 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 104 2 17 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 104 (Polychromatic418967fa.accept_16_1_4_8_1_3434
  33 68 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 104 4 8 17 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 104 (accept_3_2 31
  68 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 104 2 15 34 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 104
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 68 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 68 104 4 7 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 68 104 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 68 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 104 2 13 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 104 (accept_3_2 25 68 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 104 4 6 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 68 104 (Polychromatic418967fa.accept_16_7_4_8_1_2487 23 68 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 104 2 11 34 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 104
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 68 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 104 4 5 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 104 (accept_3_2 19 68 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  104 2 9 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 104 (Polychromatic418967fa.accept_16_1_4_8_1_3434 17 68 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 104 4 4 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 104 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 104 2 7 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 104 (accept_3_2 13 68 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 104 4 3 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 68 104 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 104 2 5 34 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 104
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 68 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 104 4 2 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 104 (accept_3_2 7 68 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 104
  2 3 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  104 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 68 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 104 4 1 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 104 (Polychromatic418967fa.accept_16_3_4_8_1_3450 3 68 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 104 2 1 34 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 104 (accept_3_2 1 68 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 104))))))))))))))))))))))))))))))))))))) (allB_succ' 38 67 104 (Eq.refl Bool.true)
  (allA_of_3_0 38 67 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 66 104 (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 66 104 2 19 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 104 (accept_3_2 37 66 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66
  104 2 18 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 104 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 66 104 2 17 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 66 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 104 2 16 33 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 104 (accept_3_2 31 66 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 104 2 15 33 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 104
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 66 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 104 2 14 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 66 104 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 104 2 13 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 104 (accept_3_2 25 66 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 104 2 12 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 104 2 11 33 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 104
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 104 2 10 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 104 (accept_3_2 19 66 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66
  104 2 9 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  66 104 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 104 2 8 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 66 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 104 2 7 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 104 (accept_3_2 13 66 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 104 2 6 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 66 104 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 104 2 5 33 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 104
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 104 2 4 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 104 (accept_3_2 7 66 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 104
  2 3 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66
  104 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 66 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 104 2 2 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 66 104 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 66 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 104 2 1 33 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 104 (accept_3_2 1 66 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 104))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 65 104 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 65 104 13 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 65 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 65 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 104 (accept_3_2 37 65 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 35
  65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 104 (accept_3_2 34 65
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 104 (Polychromatic418967fa.accept_6_3_5_2_1_12
  33 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 104
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 104 (accept_3_2 31 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 104 (accept_3_2 28 65 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 65 104 13 2 5 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 65 104 (accept_3_2 25 65 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 104
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 104 (accept_3_2 22 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 104 (Polychromatic418967fa.accept_16_4_1_8_1_835 20 65 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 104 (accept_3_2 19 65 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 104
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 104 (accept_3_2 16 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 104 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 65 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 65 104 13 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 65 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 12
  65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 104
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 104 (accept_3_2 10 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 104 (accept_3_2 7 65 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 65 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 104
  (Polychromatic418967fa.accept_17_5_14_2_1_4568 5 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 104 (accept_3_2 4 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 104 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 65 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 104 (accept_3_2 1 65 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 104)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 64 104 (Eq.refl Bool.true)
  (allA_of_3_0 41 64 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 63 104 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 104 (accept_3_2 40 63 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 104 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 104 (Polychromatic418967fa.accept_17_4_12_2_1_2349
  38 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 104 (accept_3_2 37
  63 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 104
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 63 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 104 (accept_3_2 34 63 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 63 104 (Polychromatic418967fa.accept_16_1_15_8_1_2411 33 63 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 104
  (Polychromatic418967fa.accept_15_2_3_14_1_972 32 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 104 (accept_3_2 31 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 104 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 104 (accept_3_2 28 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 104 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 63 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 104
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 104 (accept_3_2 25 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 104 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 104 (accept_3_2 22 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 104 (Polychromatic418967fa.accept_17_4_12_2_1_2349 21 63 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 104
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 20 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 104 (accept_3_2 19 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 104 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 104 (accept_3_2 16 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 104 (Polychromatic418967fa.accept_14_1_7_6_1_3604 15 63 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 104
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 104 (accept_3_2 13 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 104 (Polychromatic418967fa.accept_16_12_15_8_1_4586 12 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 104 (accept_3_2 10 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 104 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 63 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 104
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 104 (accept_3_2 7 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  104 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 104 (accept_3_2 4 63 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 104 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 63 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 104 (Polychromatic418967fa.accept_11_2_8_5_1_1219 2
  63 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 104 (accept_3_2 1 63 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 104)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 62
  104 (Eq.refl Bool.true) (allA_succ_of_gcd 42 62 104 2 21 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 104 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 62 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 104 2 20 31 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 104
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 104 2 19 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 62 104 (accept_3_2 37 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62
  104 2 18 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  62 104 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 62 104 2 17 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 62 104 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 62 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 104 2 16 31 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 104 (accept_3_2 31 62 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62 104 2 15 31 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 62 104
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 62 104 2 14 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 62 104 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 62 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 104 2 13 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 104 (accept_3_2 25 62 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 104 2 12 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 104 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 62 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 104 2 11 31 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 104
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 104 2 10 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 62 104 (accept_3_2 19 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62
  104 2 9 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  62 104 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 62 104 2 8 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 62 104 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 62 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 104 2 7 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 104 (accept_3_2 13 62 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 104 2 6 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 62 104 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 62 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 62 104 2 5 31 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 62 104
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 62 104 2 4 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 62 104 (accept_3_2 7 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 104
  2 3 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 62
  104 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 62 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 62 104 2 2 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 62 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 62 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 104 2 1 31 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 104 (accept_3_2 1 62 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 104))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 61 104 (Eq.refl Bool.true)
  (allA_of_3_0 44 61 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 60 104 (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 60 104 4 11 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 60 104 (accept_3_2 43 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60
  104 2 21 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  60 104 (Polychromatic418967fa.accept_16_9_12_8_1_1554 41 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 60 104 4 10 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 60 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 104 2 19 30 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 104 (accept_3_2 37 60 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 104 4 9 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 104 (Polychromatic418967fa.accept_9_8_6_5_1_513 35
  60 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 104 2 17 30 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 104
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 104 4 8 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 104 (accept_3_2 31 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  104 2 15 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 104 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 104 4 7 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 104 (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 60 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 104 2 13 30 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 104 (accept_3_2 25 60 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 104 4 6 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 23
  60 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 104 2 11 30 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 104
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 104 4 5 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 104 (accept_3_2 19 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  104 2 9 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 104 4 4 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 104 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 60 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 104 2 7 30 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 104 (accept_3_2 13 60 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 104 4 3 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 104 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 104 2 5 30 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 104
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 104 4 2 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 104 (accept_3_2 7 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 104
  2 3 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  104 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 104 4 1 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 104 2 1 30 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 104 (accept_3_2 1 60 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 104))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 59 104 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 59 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 104 (accept_3_2 43 59 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 104 (Polychromatic418967fa.accept_19_4_2_9_1_4584
  42 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 104
  (Polychromatic418967fa.accept_22_19_15_16_1_4583 41 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 59 104 (accept_3_2 40 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 59 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 104 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 59 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 104 (accept_3_2 37 59 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 104 (Polychromatic418967fa.accept_16_4_11_8_1_1574
  36 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 104
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 104 (accept_3_2 34 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 104 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 104 (accept_3_2 31 59 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 104
  (Polychromatic418967fa.accept_16_13_11_8_1_2449 29 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 104 (accept_3_2 28 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 104 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 59 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 104 (accept_3_2 25 59 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 104 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 59 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 104
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 104 (accept_3_2 22 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 104 (Polychromatic418967fa.accept_16_4_11_8_1_1574 20 59 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 104 (accept_3_2 19 59 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 104 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 104
  (Polychromatic418967fa.accept_19_17_2_9_1_4582 17 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 104 (accept_3_2 16 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 104 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 104 (accept_3_2 13 59 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 104 (Polychromatic418967fa.accept_16_12_11_8_1_832 12 59 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 104
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 104 (accept_3_2 10 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 104 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 59 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 104 (accept_3_2 7 59 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 104 (Polychromatic418967fa.accept_23_6_13_12_1_4581 6 59 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 104
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 104 (accept_3_2 4 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 104 (accept_3_2 1 59 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 104)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 58 104 (Eq.refl Bool.true)
  (allA_of_3_0 47 58 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 57 104 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 57 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 104 (accept_3_2 46 57 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 104 (Polychromatic418967fa.accept_18_9_3_14_1_3361 45 57 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 104
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 104 (accept_3_2 43 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 104 (accept_3_2 40 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 104 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 57 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 104
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 104 (accept_3_2 37 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 104 (Polychromatic418967fa.accept_16_4_9_8_1_2509 36 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 104 (accept_3_2 34 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 104
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 104 (accept_3_2 31 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 104 (accept_3_2 28 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 104 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 57 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 104
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 104 (accept_3_2 25 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 104 (accept_3_2 22 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 104 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 57 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 104
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 104 (accept_3_2 19 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 104 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 104 (accept_3_2 16 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 104
  (Polychromatic418967fa.accept_21_14_15_20_1_4541 14 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 57 104 (accept_3_2 13 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 104 (accept_3_2 10 57 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 9
  57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 104
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 104 (accept_3_2 7 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  104 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 104 (accept_3_2 4 57 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 104 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 57 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  57 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 104 (accept_3_2 1 57 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 104)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  49 56 104 (Eq.refl Bool.true) (allA_succ_of_gcd 48 56 104 8 6 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 104 (Polychromatic418967fa.accept_18_11_2_14_1_3351 47 56
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 104 2 23 28 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 104
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 104 4 11 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 56 104 (accept_3_2 43 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  104 2 21 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 104 (Polychromatic418967fa.accept_19_3_18_9_1_4580 41 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 56 104 8 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 56 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 56 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 104 2 19 28 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 104 (accept_3_2 37 56 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 104 4 9 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 56 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 104 2 17 28 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 104
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 104 8 4 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 104 (accept_3_2 31 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  104 2 15 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  56 104 (Polychromatic418967fa.accept_18_11_2_14_1_3351 29 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 104 4 7 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 104 (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 56 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 104 2 13 28 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 104 (accept_3_2 25 56 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 104 8 3 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 104 (Polychromatic418967fa.accept_21_2_14_20_1_841
  23 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 104 2 11 28 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 104
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 104 4 5 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 104 (accept_3_2 19 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  104 2 9 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 104 8 2 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 56 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 104 2 7 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 104 (accept_3_2 13 56 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 104 4 3 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 104 (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 56 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 104 2 5 28 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 104
  (Polychromatic418967fa.accept_21_9_14_20_1_4579 9 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 104 8 1 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 104 (accept_3_2 7 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 104
  2 3 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  104 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 56 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 104 4 1 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 104 2 1 28 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 104 (accept_3_2 1 56 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 104))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 55 104 (Eq.refl
  Bool.true) (allA_of_3_0 50 55 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 54 104 (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 54 104 2 25 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 104 (accept_3_2 49 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54
  104 2 24 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  54 104 (Polychromatic418967fa.accept_22_3_10_16_1_4578 47 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 54 104 2 23 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 54 104 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 54 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 104 2 22 27 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 104 (accept_3_2 43 54 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 104 2 21 27 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 104
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 104 2 20 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 54 104 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 104 2 19 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 104 (accept_3_2 37 54 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 104 2 18 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 104 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 54 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 104 2 17 27 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 104
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 104 2 16 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 104 (accept_3_2 31 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54
  104 2 15 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  54 104 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 54 104 2 14 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 54 104 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 54 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 104 2 13 27 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 104 (accept_3_2 25 54 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 104 2 12 27 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 104
  (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 104 2 11 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 54 104 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 104 2 10 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 104 (accept_3_2 19 54 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 104 2 9 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 54 104 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 54 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 104 2 8 27 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 104
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 104 2 7 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 104 (accept_3_2 13 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  104 2 6 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 104 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 104 2 5 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 104 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 54 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 104 2 4 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 104 (accept_3_2 7 54 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 104 2 3 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 104 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 54 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 104 2 2 27 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 104
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 104 2 1 27 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 104 (accept_3_2 1 54 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  104))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 53 104 (Eq.refl Bool.true) (allA_succ_of_accept
  51 53 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 104 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 104 (accept_3_2 49 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 53 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 104
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 104 (accept_3_2 46 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 104 (accept_3_2 43 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 104 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 104
  (Polychromatic418967fa.accept_19_3_15_9_1_4576 41 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 104 (accept_3_2 40 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 104 (accept_3_2 37 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 104 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 53 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 104
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 104 (accept_3_2 34 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 104 (Polychromatic418967fa.accept_19_13_15_9_1_3293 32 53 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 104 (accept_3_2 31 53 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 104
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 104 (accept_3_2 28 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 104 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 104 (accept_3_2 25 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 104
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 104 (accept_3_2 22 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 104 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 104 (accept_3_2 19 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 104 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 53 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 104
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 104 (accept_3_2 16 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 104 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 104 (accept_3_2 13 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 104 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 104
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 104 (accept_3_2 10 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 104 (Polychromatic418967fa.accept_21_8_11_20_1_4574 8 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 104 (accept_3_2 7 53 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 104 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 53 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 104
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 104 (accept_3_2 4 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 53 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 104 (accept_3_2 1 53 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 104)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 104 (allA_of_3_0 52 52
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 104 (allA_succ_of_accept 50 51 104
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 104 (accept_3_2 49 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 104 (accept_3_2 46 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 104
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 104 (accept_3_2 43 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 104 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 104 (accept_3_2 40 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 104
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 104 (accept_3_2 37 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 104 (accept_3_2 34 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 104 (Polychromatic418967fa.accept_20_13_11_4_1_2042 33 51 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 104
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 104 (accept_3_2 31 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 104 (accept_3_2 28 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 104 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 51 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 104
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 104 (accept_3_2 25 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 104 (accept_3_2 22 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 104
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 104 (accept_3_2 19 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 104 (accept_3_2 16 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 104
  (Polychromatic418967fa.accept_21_14_9_20_1_4573 14 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 104 (accept_3_2 13 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 104 (accept_3_2 10 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 104 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 51 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 104
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 104 (accept_3_2 7 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  104 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 104 (accept_3_2 4 51 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 104 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  51 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 104 (accept_3_2 1 51 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 104)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 104 (allA_succ_of_accept 49 50 104 (accept_3_2 49 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 104 2 24 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 50 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 50 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 104 2 23 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 104 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  45 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 104 2 22 25 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 104 (accept_3_2 43
  50 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 104 2 21 25 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 104
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 104 2 20 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 104 (Polychromatic418967fa.accept_15_9_5_14_1_973 39 50 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 104 2 19 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 104 (accept_3_2 37 50 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 104 2 18 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 104 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 50 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 104 2 17 25 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 104
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 104 2 16 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 104 (accept_3_2 31 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  104 2 15 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 104 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 104 2 14 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 104 (Polychromatic418967fa.accept_24_3_2_8_1_4572 27 50 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 104 2 13 25 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 104 (accept_3_2 25 50 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 104 2 12 25 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 104
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 104 2 11 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 104 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 50 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 104 2 10 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 104 (accept_3_2 19 50 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 104 2 9 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 104 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 50 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 104 2 8 25 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 104
  (Polychromatic418967fa.accept_20_15_10_4_1_4571 15 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 104 2 7 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 104 (accept_3_2 13 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  104 2 6 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 104 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 104 2 5 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 50 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 104 2 4 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 104 (accept_3_2 7 50 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 104 2 3 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 50 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 104 2 2 25 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 104
  (Polychromatic418967fa.accept_19_3_12_9_1_3308 3 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 104 2 1 25 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 104 (accept_3_2 1 50 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  104)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 104 (allA_of_3_0 49 49 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 104 (allA_succ_of_accept 47 48 104 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 104 2 23 24 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 104
  (Polychromatic418967fa.accept_19_7_10_9_1_2162 45 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 104 4 11 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 104 (accept_3_2 43 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48
  104 2 21 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  48 104 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 104 8 5 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 48 104 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 48 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 104 2 19 24 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 104 (accept_3_2 37 48 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 104 4 9 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 104 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 104 2 17 24 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 104
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 104 8 4 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 104 (accept_3_2 31 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  104 2 15 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  48 104 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 104 4 7 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 104 (Polychromatic418967fa.accept_23_4_2_12_1_4570 27 48 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 104 2 13 24 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 104 (accept_3_2 25 48 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 104 8 3 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 104 (Polychromatic418967fa.accept_19_4_10_9_1_4569 23 48 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 104 2 11 24 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 104
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 104 4 5 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 104 (accept_3_2 19 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  104 2 9 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 104 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 104 8 2 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 104 2 7 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 104 (accept_3_2 13 48 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 104 4 3 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 48 104 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 48 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 104 2 5 24 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 104
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 104 8 1 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 104 (accept_3_2 7 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 104
  2 3 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  104 (Polychromatic418967fa.accept_17_5_14_2_1_4568 5 48 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 104 4 1 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 104 (Polychromatic418967fa.accept_17_3_14_2_1_646 3 48 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 104 2 1 24 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 104 (accept_3_2 1 48 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 48 104)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 104
  (allA_succ_of_accept 46 47 104 (accept_3_2 46 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 104 (accept_3_2 43 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 104
  (Polychromatic418967fa.accept_10_1_7_4_1_968 41 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 104 (accept_3_2 40 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 104 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 104 (accept_3_2 37 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 104 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 104
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 104 (accept_3_2 34 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 104 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 104 (accept_3_2 31 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 47 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 104
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 104 (accept_3_2 28 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 104 (accept_3_2 25 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 104
  (Polychromatic418967fa.accept_10_3_7_4_1_584 23 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 104 (accept_3_2 22 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 104 (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 47 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 104 (accept_3_2 19 47 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 104 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 104
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 104 (accept_3_2 16 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 104 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 104 (accept_3_2 13 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 104
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 104 (accept_3_2 10 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 104 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 104 (accept_3_2 7 47 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 104
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 104 (accept_3_2 4 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 104 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 47 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 104 (accept_3_2 1 47 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 104))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 104 (allA_of_3_0 46 46 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 104 (allA_succ_of_accept 44 45 104
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 104 (accept_3_2 43 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 104 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 104 (accept_3_2 40 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 104 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 45 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 104
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 104 (accept_3_2 37 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 104 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 104 (accept_3_2 34 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 104 (Polychromatic418967fa.accept_21_12_3_20_1_4567 33 45 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 104
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 104 (accept_3_2 31 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 104 (accept_3_2 28 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 104 (Polychromatic418967fa.accept_16_11_13_8_1_1578 27 45 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 104
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 104 (accept_3_2 25 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 104 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 104 (accept_3_2 22 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 104 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 104
  (Polychromatic418967fa.accept_16_4_13_8_1_3424 20 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 104 (accept_3_2 19 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 104 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 104 (accept_3_2 16 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 104 (Polychromatic418967fa.accept_20_15_5_4_1_4566 15 45 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 104
  (Polychromatic418967fa.accept_24_14_21_8_1_4565 14 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 104 (accept_3_2 13 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 104 (Polychromatic418967fa.accept_16_12_13_8_1_2409 12 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 104 (accept_3_2 10 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 104
  (Polychromatic418967fa.accept_17_8_11_2_1_3415 8 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 104 (accept_3_2 7 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  104 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 45 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 104 (accept_3_2 4 45 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 104 (Polychromatic418967fa.accept_16_3_13_8_1_1594 3 45 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 45
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 104 (accept_3_2 1 45 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 104))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  104 (allA_succ_of_accept 43 44 104 (accept_3_2 43 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 104 2 21 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 44 104 (Polychromatic418967fa.accept_16_9_12_8_1_1554 41 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 104 4 10 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 104 2 19 22 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 104 (accept_3_2 37 44 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 104 4 9 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 104 (Polychromatic418967fa.accept_16_3_12_8_1_808
  35 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 104 2 17 22 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 104
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 104 4 8 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 104 (accept_3_2 31 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  104 2 15 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 104 4 7 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 104 (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 44 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 104 2 13 22 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 104 (accept_3_2 25 44 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 104 4 6 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 104 (Polychromatic418967fa.accept_16_7_12_8_1_2450
  23 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 104 2 11 22 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 104
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 104 4 5 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 104 (accept_3_2 19 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  104 2 9 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 104 4 4 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 44 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 104 2 7 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 104 (accept_3_2 13 44 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 104 4 3 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 104 2 5 22 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 104
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 104 4 2 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 104 (accept_3_2 7 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 104
  2 3 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  104 (Polychromatic418967fa.accept_16_5_12_8_1_2521 5 44 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 44 104 4 1 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 44 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 104 2 1 22 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 104 (accept_3_2 1 44 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 44 104)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 104 (allA_of_3_0 43 43
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 104 (allA_succ_of_accept 41 42 104
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 41 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 42 104 2 20 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 42 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 104 2 19 21 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 104 (accept_3_2 37 42 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 104 2 18 21 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 104
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 104 2 17 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 42 104 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 104 2 16 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 104 (accept_3_2 31 42 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 104 2 15 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 104 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 104 2 14 21 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 104
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 104 2 13 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 42 104 (accept_3_2 25 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42
  104 2 12 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  42 104 (Polychromatic418967fa.accept_24_23_18_8_1_4564 23 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 42 104 2 11 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 42 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 104 2 10 21 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 104 (accept_3_2 19 42 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 104 2 9 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 104 (Polychromatic418967fa.accept_9_8_6_5_1_513 17
  42 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 104 2 8 21 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 104
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 42 104 2 7 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 104 (accept_3_2 13 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42
  104 2 6 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  42 104 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 42 104 2 5 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 42 104 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 104 2 4 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 104 (accept_3_2 7 42 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 104 2 3 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 42 104 (Polychromatic418967fa.accept_19_5_4_9_1_4563 5 42 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 104 2 2 21 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 104
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 104 2 1 21 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 104 (accept_3_2 1 42 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  104)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 104 (allA_succ_of_accept 40 41 104 (accept_3_2 40 41 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 104
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 104 (accept_3_2 37 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 104 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 104 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 41 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 104 (accept_3_2 34 41 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 104
  (Polychromatic418967fa.accept_17_15_7_2_1_2303 32 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 104 (accept_3_2 31 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 104 (Polychromatic418967fa.accept_17_13_7_2_1_4562 30 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 104 (Polychromatic418967fa.accept_17_12_7_2_1_4561 29 41 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 104 (accept_3_2 28 41 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 104
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 104 (accept_3_2 25 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 104 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 104 (Polychromatic418967fa.accept_16_7_9_8_1_829 23 41 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 104 (accept_3_2 22 41 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 104
  (Polychromatic418967fa.accept_16_4_9_8_1_2509 20 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 104 (accept_3_2 19 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 104 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 104 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 41 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 104 (accept_3_2 16 41 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 104
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 104 (accept_3_2 13 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 104 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 104 (Polychromatic418967fa.accept_18_11_5_14_1_4560 11 41 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 104 (accept_3_2 10 41 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 104
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 8 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 104 (accept_3_2 7 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  104 (Polychromatic418967fa.accept_19_6_3_9_1_3332 6 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 41 104 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 41 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 104 (accept_3_2 4 41 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 104
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 41 104 (accept_3_2 1 41 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41
  104))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 104 (allA_of_3_0 40 40 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 39 104 (allA_succ_of_accept 38 39 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 104 (accept_3_2 37 39 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 104 (Polychromatic418967fa.accept_15_6_9_14_1_3457
  36 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 39 104 (accept_3_2 34 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  39 104 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 39 104 (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 39 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 104 (accept_3_2 31 39 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 104 (accept_3_2 28 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  39 104 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 39 104 13 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 39 104 (accept_3_2 25 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 104 (accept_3_2 22 39 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 104 (Polychromatic418967fa.accept_11_10_6_5_1_1239
  21 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 104
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 104 (accept_3_2 19 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 104 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 104 (accept_3_2 16 39 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 104
  (Polychromatic418967fa.accept_17_14_5_2_1_4559 14 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 39 104 13 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 39 104 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 104 (accept_3_2 10 39 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 9
  39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 104
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 104 (accept_3_2 7 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  104 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 104 (accept_3_2 4 39 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  39 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 104 (accept_3_2 1 39 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 104))))))))))))))))))))))))))))))))))))))) (allB_succ 38 104
  (allA_succ_of_accept 37 38 104 (accept_3_2 37 38 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  104 2 18 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 104 2 17 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 38 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 104 2 16 19 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 104 (accept_3_2 31 38 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 104 2 15 19 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 104
  (Polychromatic418967fa.accept_10_9_8_4_1_970 29 38 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 104 2 14 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 104 (Polychromatic418967fa.accept_23_4_15_12_1_4558 27 38 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 104 2 13 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 104 (accept_3_2 25 38 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 104 2 12 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 104 2 11 19 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 104
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 38 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 104 2 10 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 104 (accept_3_2 19 38 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  104 2 9 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 104 2 8 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 38 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 104 2 7 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 104 (accept_3_2 13 38 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 104 2 6 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 104 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 104 2 5 19 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 104
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 38 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 104 2 4 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 104 (accept_3_2 7 38 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 104
  2 3 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  104 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 38 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 104 2 2 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 104 2 1 19 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 104 (accept_3_2 1 38 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 104)))))))))))))))))))))))))))))))))))))) (allB_succ 37 104 (allA_of_3_0 37 37 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 104 (allA_succ_of_accept 35 36 104
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 36 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 104 2 17 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 104 4 8 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 104 (accept_3_2 31 36 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 104 2 15 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 36 104 (Polychromatic418967fa.accept_16_13_4_8_1_4557 29 36 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 104 4 7 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 104
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 36 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 104 2 13 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 104 (accept_3_2 25 36 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  104 4 6 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 104 2 11 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 104 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 36 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 104 4 5 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 104 (accept_3_2 19 36 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 104 2 9 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 104 (Polychromatic418967fa.accept_16_1_4_8_1_3434 17 36 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 104 4 4 9 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 104
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 36 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 104 2 7 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 104 (accept_3_2 13 36 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  104 4 3 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 104 (Polychromatic418967fa.accept_16_11_4_8_1_3435 11 36 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 104 2 5 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 104 4 2 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 104 (accept_3_2 7 36 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 104 2 3 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 104 4 1 9 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 104
  (Polychromatic418967fa.accept_16_3_4_8_1_3450 3 36 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 104 2 1 18 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 104 (accept_3_2 1 36 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  104)))))))))))))))))))))))))))))))))))) (allB_succ 35 104 (allA_succ_of_accept 34 35 104 (accept_3_2 34 35 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 104
  (Polychromatic418967fa.accept_15_2_5_14_1_61 32 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 104 (accept_3_2 31 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 104 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 35 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 104 (accept_3_2 28 35 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 104
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 104 (accept_3_2 25 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 104 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 104 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 35 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 104 (accept_3_2 22 35 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 104
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 104 (accept_3_2 19 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 104 (Polychromatic418967fa.accept_19_18_16_9_1_4556 18 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 104 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 35 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 104 (accept_3_2 16 35 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 104
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 104 (accept_3_2 13 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 104 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 104 (accept_3_2 10 35 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 104
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 104 (accept_3_2 7 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  104 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 104 (Polychromatic418967fa.accept_16_5_3_8_1_4555 5 35 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 104 (accept_3_2 4 35 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 104 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  35 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 104 (accept_3_2 1 35 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 104))))))))))))))))))))))))))))))))))) (allB_succ 34 104
  (allA_of_3_0 34 34 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 104 (allA_succ_of_accept 32 33 104
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 104 (accept_3_2 31 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 104 (accept_3_2 28 33 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 104 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 33 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 104
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 104 (accept_3_2 25 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 104 (Polychromatic418967fa.accept_19_5_14_9_1_4554 24 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 104 (accept_3_2 22 33 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 104
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 104 (accept_3_2 19 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 104 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 104 (accept_3_2 16 33 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 104 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 104
  (Polychromatic418967fa.accept_17_14_16_2_1_4553 14 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 104 (accept_3_2 13 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 104 (accept_3_2 10 33 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 104 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 33 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 104
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 104 (accept_3_2 7 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  104 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 104 (accept_3_2 4 33 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 104 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  33 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 104 (accept_3_2 1 33 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 104))))))))))))))))))))))))))))))))) (allB_succ 32 104
  (allA_succ_of_accept 31 32 104 (accept_3_2 31 32 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  104 2 15 16 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 104 (Polychromatic418967fa.accept_19_10_13_9_1_4552 29 32 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 104 4 7 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 104 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 32 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 104 2 13 16 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 104 (accept_3_2 25 32 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 104 8 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 32 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 104 2 11 16 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 104
  (Polychromatic418967fa.accept_17_4_15_2_1_4551 21 32 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 104 4 5 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 104 (accept_3_2 19 32 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  104 2 9 16 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 104 8 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 104 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 32 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 104 2 7 16 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 104 (accept_3_2 13 32 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 104 4 3 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 104 (Polychromatic418967fa.accept_23_11_9_12_1_4550 11 32 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 104 2 5 16 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 104
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 104 8 1 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 104 (accept_3_2 7 32 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 104
  2 3 16 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  104 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 104 4 1 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 104 2 1 16 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 104 (accept_3_2 1 32 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 104)))))))))))))))))))))))))))))))) (allB_succ 31 104 (allA_of_3_0 31 31 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 104 (allA_succ_of_accept 29 30 104
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 104 2 14 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 104 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 30 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 104 2 13 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 104 (accept_3_2 25 30 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 104 2 12 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 104 (Polychromatic418967fa.accept_17_6_13_2_1_4549 23 30 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 104 2 11 15 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 104
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 104 2 10 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 104 (accept_3_2 19 30 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30
  104 2 9 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  30 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 30 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 104 2 8 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 30 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 104 2 7 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 104 (accept_3_2 13 30 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 104 2 6 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 30 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 104 2 5 15 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 104
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 104 2 4 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 104 (accept_3_2 7 30 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 104
  2 3 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30
  104 (Polychromatic418967fa.accept_20_5_10_4_1_4548 5 30 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 104 2 2 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 104 2 1 15 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 104 (accept_3_2 1 30 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 30 104)))))))))))))))))))))))))))))) (allB_succ 29 104 (allA_succ_of_accept 28 29 104
  (accept_3_2 28 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 104
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 29 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 104 (accept_3_2 25 29 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 29 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 23
  29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 104 (accept_3_2 22 29
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 104 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 104
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 104 (accept_3_2 19 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 104 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 29 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 104 (accept_3_2 16 29 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 104
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 104 (accept_3_2 13 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 104 (Polychromatic418967fa.accept_16_11_13_8_1_1578 11 29 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 104 (accept_3_2 10 29 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 104
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 104 (accept_3_2 7 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  104 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 104 (accept_3_2 4 29 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  29 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 104 (accept_3_2 1 29 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 104))))))))))))))))))))))))))))) (allB_succ 28 104 (allA_of_3_0
  28 28 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 104 (allA_succ_of_accept 26 27 104
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 104 (accept_3_2 25 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 104 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 104 (accept_3_2 22 27 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 104 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 27 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 104
  (Polychromatic418967fa.accept_16_4_11_8_1_1574 20 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 104 (accept_3_2 19 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 104 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 104 (accept_3_2 16 27 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 104 (Polychromatic418967fa.accept_17_15_10_2_1_2309 15 27 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 104
  (Polychromatic418967fa.accept_19_14_8_9_1_4547 14 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 104 (accept_3_2 13 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 104 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 104 (accept_3_2 10 27 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 104 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 27 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 104
  (Polychromatic418967fa.accept_17_8_10_2_1_4546 8 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 104 (accept_3_2 7 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  104 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 104 (accept_3_2 4 27 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 104 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 27 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 104 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  27 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 104 (accept_3_2 1 27 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 104))))))))))))))))))))))))))) (allB_succ 26 104
  (allA_succ_of_accept 25 26 104 (accept_3_2 25 26 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  104 2 12 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 104 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 26 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 104 2 11 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 104 2 10 13 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 104 (accept_3_2 19 26 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 104 2 9 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 104 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  26 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 104 2 8 13 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 104
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 26 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 104 2 7 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 13 26 104 13 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 26 104 2 6 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 26 104 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 104 2 5 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 104 (Polychromatic418967fa.accept_22_9_4_16_1_4545 9 26 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 104 2 4 13 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 104 (accept_3_2 7 26 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 104 2 3 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26 104 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 26
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 104 2 2 13 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 104
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 26 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 104 2 1 13 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 104 (accept_3_2 1 26 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  104)))))))))))))))))))))))))) (allB_succ 25 104 (allA_of_3_0 25 25 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 104 (allA_succ_of_accept 23 24 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 104 2 11 12 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 104
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 104 4 5 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 104 (accept_3_2 19 24 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  104 2 9 12 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 104 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 104 8 2 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 104 (Polychromatic418967fa.accept_17_15_7_2_1_2303 15 24 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 104 2 7 12 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 104 (accept_3_2 13 24 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 104 4 3 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 104 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 104 2 5 12 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 104
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 104 8 1 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 104 (accept_3_2 7 24 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 104
  2 3 12 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  104 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 24 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 104 4 1 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 104 2 1 12 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 104 (accept_3_2 1 24 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 24 104)))))))))))))))))))))))) (allB_succ 23 104 (allA_succ_of_accept 22 23 104
  (accept_3_2 22 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 104
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 104 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 23 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 104 (accept_3_2 19 23 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  23 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 104 (accept_3_2 16 23
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 104 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 104
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 104 (accept_3_2 13 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 104 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 104 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 104 (accept_3_2 10 23 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 104
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 104 (accept_3_2 7 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  104 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 23 104 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 23 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 104 (accept_3_2 4 23 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 104
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 104 (accept_3_2 1 23 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  104))))))))))))))))))))))) (allB_succ 22 104 (allA_of_3_0 22 22 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 21 104 (allA_succ_of_accept 20 21 104 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 104 (accept_3_2 19 21 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 104 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 104 (accept_3_2 16 21 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 104 (Polychromatic418967fa.accept_23_14_21_12_1_4544 14 21 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 104 (accept_3_2 13 21 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 104 (Polychromatic418967fa.accept_16_12_5_8_1_2492 12 21
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 104 (accept_3_2 10 21 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 104 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 21 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 104 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 104 (accept_3_2 7 21 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 104 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 104
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 104 (accept_3_2 4 21 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  104 (Polychromatic418967fa.accept_16_3_5_8_1_4543 3 21 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 104 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 104 (accept_3_2 1 21 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 104))))))))))))))))))))) (allB_succ 20 104 (allA_succ_of_accept 19 20 104
  (accept_3_2 19 20 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 104 2 9 10 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 104
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 104 4 4 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 20 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 104 2 7 10 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 104 (accept_3_2 13 20 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 104 4 3 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 104 (Polychromatic418967fa.accept_16_11_4_8_1_3435 11 20 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 104 2 5 10 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 104 (Polychromatic418967fa.accept_15_9_5_14_1_973 9
  20 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 104 4 2 5 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 104 (accept_3_2 7 20
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 104 2 3 10 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 104
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 5 20 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 104 4 1 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 104 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 20 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 104 2 1 10 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 104 (accept_3_2 1 20 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 104)))))))))))))))))))) (allB_succ 19 104 (allA_of_3_0 19 19 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 104 (allA_succ_of_accept 17 18 104 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 18 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 104 2 8 9 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 104
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 18 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 104 2 7 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 104 (accept_3_2 13 18 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  104 2 6 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 104 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 18 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 104 2 5 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 104 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 104 2 4 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 104 (accept_3_2 7 18 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 104 2 3 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 104 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 104 2 2 9 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 104
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 104 2 1 9 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 104 (accept_3_2 1 18 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  104)))))))))))))))))) (allB_succ 17 104 (allA_succ_of_accept 16 17 104 (accept_3_2 16 17 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 104
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 17 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 104 (accept_3_2 13 17 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 104 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 104 (accept_3_2 10 17 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 104
  (Polychromatic418967fa.accept_19_8_17_9_1_4542 8 17 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 104 (accept_3_2 7 17 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  104 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 17 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 104 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 17 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 104 (accept_3_2 4 17 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 17
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 104 (accept_3_2 1 17 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 104))))))))))))))))) (allB_succ 16 104 (allA_of_3_0 16 16 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 104 (allA_succ_of_accept 14 15 104
  (Polychromatic418967fa.accept_21_14_15_20_1_4541 14 15 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 15 104 (accept_3_2 13 15 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 104 (accept_3_2 10 15 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 9
  15 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 104
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 104 (accept_3_2 7 15 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  104 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 15 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 104 (accept_3_2 4 15 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 104 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 15 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 104 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  15 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 104 (accept_3_2 1 15 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 104))))))))))))))) (allB_succ 14 104 (allA_succ_of_accept 13 14
  104 (accept_3_2 13 14 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 104 2 6 7 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 104
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 104 2 5 7 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 104 (Polychromatic418967fa.accept_20_9_14_4_1_4540 9 14 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 104 2 4 7 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 104 (accept_3_2 7 14 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 104 2 3 7 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 104 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 104 2 2 7 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 104 (Polychromatic418967fa.accept_17_3_14_2_1_646 3
  14 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 104 2 1 7 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 104 (accept_3_2 1 14
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 104)))))))))))))) (allB_succ 13 104 (allA_of_3_0 13 13 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 104 (allA_succ_of_accept 11 12 104
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 104 2 5 6 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 104 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 12 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 104 4 2 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 104 (accept_3_2 7 12 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 104 2 3 6 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 104 (Polychromatic418967fa.accept_16_5_12_8_1_2521 5 12 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 104 4 1 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 104 (Polychromatic418967fa.accept_16_3_12_8_1_808 3
  12 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 104 2 1 6 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 104 (accept_3_2 1 12
  104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 104)))))))))))) (allB_succ 11 104 (allA_succ_of_accept 10 11
  104 (accept_3_2 10 11 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 104
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 104 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 104 (accept_3_2 7 11 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 104 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 11 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 104 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  11 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 104 (accept_3_2 4 11 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 104
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 11 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 104 (accept_3_2 1 11 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  104))))))))))) (allB_succ 10 104 (allA_of_3_0 10 10 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 104
  (allA_succ_of_accept 8 9 104 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 104 (accept_3_2 7 9 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 104 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 9 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 104 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 104 (accept_3_2 4 9 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 104 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9
  104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 104
  (Polychromatic418967fa.accept_20_2_9_4_1_4539 2 9 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 104 (accept_3_2 1 9 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 104)))))))))
  (allB_succ 8 104 (allA_succ_of_accept 7 8 104 (accept_3_2 7 8 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 104 2 3 4 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 104 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 104 4 1 2 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 104 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 8 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 104 2 1 4 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 104 (accept_3_2 1 8 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 104)))))))) (allB_succ 7 104 (allA_of_3_0 7 7 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 104 (allA_succ_of_accept 5 6 104 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 6 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 104 2 2 3 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 104
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 6 104 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 104 2 1 3 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 104 (accept_3_2 1 6 104 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 104))))))
  (allB_succ 5 104 (allA_succ_of_accept 4 5 104 (accept_3_2 4 5 104 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 104 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 104 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 104 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 5 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 104 (accept_3_2 1 5 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 104))))) (allB_succ 4 104 (allA_of_3_0 4 4 104 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 104 (allA_succ_of_accept 2 3 104 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 104
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 104 (accept_3_2 1 3 104 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 104))) (allB_succ 2 104 (allA_succ_of_accept 1 2 104 (accept_3_2 1 2 104
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 104)) (allB_two
  104))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


