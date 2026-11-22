-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch181
-- name    : Polychromatic418967fa_Branch181
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:18:53.763025+00:00
-- url     : https://prove2.me/theorems/827d0491-8b38-4aa1-a26b-e490a74c275d
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch181_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_181 : allB 181 181 :=
  allB_succ' 2 180 181 (Eq.refl Bool.true) (allA_succ_of_accept 1 180 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1
  180 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 181)) (allB_succ' 3 179 181
  (Eq.refl Bool.true) (allA_of_3_1 3 179 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 178 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 178 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 181 (accept_3_3 2 178 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 178 181 (Polychromatic418967fa.accept_17_1_8_11_1_6471 1 178 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 181)))) (allB_succ' 5 177 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 177 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 177 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 181 (accept_3_3 2 177 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1
  177 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 181))))) (allB_succ' 6 176 181
  (Eq.refl Bool.true) (allA_of_3_1 6 176 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 175 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 175 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 181 (accept_3_3 5 175 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 181 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 175 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 175 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 181 (accept_3_3 2 175 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 181 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 175 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 181))))))) (allB_succ' 8 174 181 (Eq.refl Bool.true) (allA_succ_of_accept 7 174 181
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 174 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 174 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 174 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 181 (accept_3_3 5 174 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 174 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 174 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 174 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  174 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 181 (accept_3_3 2 174
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 181
  (Polychromatic418967fa.accept_13_1_5_12_1_306 1 174 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 174 181)))))))) (allB_succ' 9 173 181 (Eq.refl Bool.true) (allA_of_3_1 9 173 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 172 181 (Eq.refl Bool.true) (allA_succ_of_accept 9 172 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 181 (accept_3_3 8 172 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 181 (Polychromatic418967fa.accept_16_7_12_5_1_734 7 172 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 181 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 172 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 181 (accept_3_3 5 172 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 181 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 172 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 181
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 181 (accept_3_3 2 172 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 172 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 181)))))))))) (allB_succ' 11 171 181 (Eq.refl Bool.true) (allA_succ_of_accept 10 171 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 171 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 171 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 171 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 181 (accept_3_3 8 171 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 171 181 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 171 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  171 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 181 (accept_3_3 5 171
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 181 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 171 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 181
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 171 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 181 (accept_3_3 2 171 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 171 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 181))))))))))) (allB_succ' 12 170 181 (Eq.refl Bool.true) (allA_of_3_1 12 170 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 169 181 (Eq.refl Bool.true) (allA_succ_of_accept 12 169 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 169 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 181 (accept_3_3 11 169 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 181 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 169 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 169 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 181 (accept_3_3 8 169 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 181 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 169 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 169 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 181 (accept_3_3 5 169 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 181 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 169 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 181 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 169 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 181 (accept_3_3 2 169 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 181 (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 169 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 181))))))))))))) (allB_succ' 14 168 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 168 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 168 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 12
  168 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 181 (accept_3_3 11
  168 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 181
  (Polychromatic418967fa.accept_23_10_7_20_1_5208 10 168 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 168 181 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 168 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 181 (accept_3_3 8 168 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 168 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 181
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 168 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 168 181 (accept_3_3 5 168 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  168 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 168 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 168 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 168 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 181 (accept_3_3 2 168 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 181 (Polychromatic418967fa.accept_19_1_16_10_1_6026 1 168 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 181)))))))))))))) (allB_succ' 15 167 181 (Eq.refl
  Bool.true) (allA_of_3_1 15 167 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 166 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 166 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 166 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 181 (accept_3_3 14 166 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 166 181 (Polychromatic418967fa.accept_23_13_5_20_1_10443 13 166 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 166 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 166 181 (accept_3_3 11 166 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 166 181 (Polychromatic418967fa.accept_25_10_16_6_1_10442 10 166 181 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 166 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 181 (accept_3_3 8 166 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 166 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 166 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 181 (accept_3_3 5 166 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 166 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 181 (accept_3_3 2 166 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 166 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 181)))))))))))))))) (allB_succ' 17 165 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 165 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 181 (Polychromatic418967fa.accept_9_6_3_1_1_155
  15 165 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 181 (accept_3_3 14
  165 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 181
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 165 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 165 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 165 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 181 (accept_3_3 11 165 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 165 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 165 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 9
  165 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 181 (accept_3_3 8 165
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 181
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 165 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 165 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 165 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 181 (accept_3_3 5 165 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 165 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  165 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 181 (accept_3_3 2 165
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 181
  (Polychromatic418967fa.accept_19_1_13_10_1_4663 1 165 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165 181))))))))))))))))) (allB_succ' 18 164 181 (Eq.refl Bool.true) (allA_of_3_1 18 164 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 163 181 (Eq.refl Bool.true) (allA_succ_of_accept 18 163 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 163 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 181 (accept_3_3 17 163 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 181 (Polychromatic418967fa.accept_22_16_9_5_1_10441 16 163 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 163 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 181 (accept_3_3 14 163 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 181 (Polychromatic418967fa.accept_20_13_3_1_1_3065 13 163 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 181
  (Polychromatic418967fa.accept_10_2_3_1_1_481 12 163 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 181 (accept_3_3 11 163 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 181 (Polychromatic418967fa.accept_21_9_16_13_1_1541 9 163 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 181 (accept_3_3 8 163 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 181 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 163 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 181
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 181 (accept_3_3 5 163 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 163 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 163 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 181 (accept_3_3 2 163 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 163 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 181))))))))))))))))))) (allB_succ' 20 162 181
  (Eq.refl Bool.true) (allA_succ_of_accept 19 162 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 162 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 181
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 162 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 162 181 (accept_3_3 17 162 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 162 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 162 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 162 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 181 (accept_3_3 14 162 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 181 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 162 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 162 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 181 (accept_3_3 11 162 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 162 181 (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 162 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 162 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 162 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 181 (accept_3_3 8 162 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 181
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 162 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 181 (accept_3_3 5 162 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 181 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 162 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 181 (accept_3_3 2 162 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 181 (Polychromatic418967fa.accept_25_1_12_6_1_10440 1 162 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 181)))))))))))))))))))) (allB_succ' 21 161 181
  (Eq.refl Bool.true) (allA_of_3_1 21 161 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 160 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 160 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 181 (accept_3_3 20 160 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 181 (Polychromatic418967fa.accept_14_5_6_13_1_3145 19 160 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 181
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 160 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 181 (accept_3_3 17 160 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 181 (Polychromatic418967fa.accept_13_3_4_12_1_36 16 160 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 181 (accept_3_3 14 160 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 160 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 160 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 181 (accept_3_3 11 160 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 181 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 160 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 181 (accept_3_3 8 160 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 181 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 160 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 160 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 181 (accept_3_3 5 160 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 160 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 181 (accept_3_3 2 160 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 181 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 160 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 181)))))))))))))))))))))) (allB_succ' 23 159 181
  (Eq.refl Bool.true) (allA_succ_of_accept 22 159 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 159 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 181 (accept_3_3 20 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 159 181 (Polychromatic418967fa.accept_25_19_9_6_1_10439 19 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 181 (accept_3_3 17 159 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 181 (accept_3_3 14 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 159 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 159 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 181 (accept_3_3 11 159 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 181 (accept_3_3 8 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 181 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 181 (accept_3_3 5 159 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 181 (accept_3_3 2 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 159 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 181))))))))))))))))))))))) (allB_succ' 24 158 181 (Eq.refl Bool.true) (allA_of_3_1 24 158
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 157 181 (Eq.refl Bool.true) (allA_succ_of_accept 24 157
  181 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 157 181 (accept_3_3 23 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 157 181 (Polychromatic418967fa.accept_19_3_5_10_1_6033 22 157 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 157 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 181 (accept_3_3 20 157 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 181 (Polychromatic418967fa.accept_11_8_3_5_1_355
  19 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 181 (accept_3_3 17 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 181 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 157 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 181 (accept_3_3 14 157 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 181 (Polychromatic418967fa.accept_19_13_5_10_1_4609 13 157 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 181
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 181 (accept_3_3 11 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 181 (Polychromatic418967fa.accept_14_10_3_13_1_1530 10 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 157 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 181 (accept_3_3 8 157 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 157 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 181 (accept_3_3 5 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 157 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 181 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 157 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 181 (accept_3_3 2 157 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 181 (Polychromatic418967fa.accept_16_1_13_5_1_2280 1 157 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 181))))))))))))))))))))))))) (allB_succ' 26 156 181
  (Eq.refl Bool.true) (allA_succ_of_accept 25 156 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 156 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 181
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 156 181 (accept_3_3 23 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 156 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 156 181 (Polychromatic418967fa.accept_18_3_12_1_1_3787 21 156 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 181 (accept_3_3 20 156 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 181 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 156
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 181
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 156 181 (accept_3_3 17 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 156 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 156 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 156 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 181 (accept_3_3 14 156 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 156 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 181
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 181 (accept_3_3 11 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 156 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 156 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 181 (accept_3_3 8 156 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 156 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 181 (accept_3_3 5 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  156 181 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 156 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 181 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 181 (accept_3_3 2 156 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 181 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 156 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 181)))))))))))))))))))))))))) (allB_succ' 27 155 181
  (Eq.refl Bool.true) (allA_of_3_1 27 155 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 154 181 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 154 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 154 181 (accept_3_3 26 154 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 154 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 154 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 181
  (Polychromatic418967fa.accept_17_7_1_11_1_1894 24 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 154 181 (accept_3_3 23 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 181 (Polychromatic418967fa.accept_25_22_4_6_1_10438 22 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 154 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 154 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 181 (accept_3_3 20 154 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 154 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 181
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 181 (accept_3_3 17 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 181 (accept_3_3 14 154 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 181 (Polychromatic418967fa.accept_16_13_10_5_1_2278 13 154 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 181
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 12 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 154 181 (accept_3_3 11 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 154 181 (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 154 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 181 (accept_3_3 8 154 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 154 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 181
  (Polychromatic418967fa.accept_19_6_2_10_1_4691 6 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 181 (accept_3_3 5 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 181 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 154 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 181 (accept_3_3 2 154 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 181 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 154 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 181)))))))))))))))))))))))))))) (allB_succ' 29 153
  181 (Eq.refl Bool.true) (allA_succ_of_accept 28 153 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 181
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 181 (accept_3_3 26 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 153 181 (Polychromatic418967fa.accept_19_6_1_10_1_7449 25 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 181 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 153 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 181 (accept_3_3 23 153 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 153 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 181
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 181 (accept_3_3 20 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 181 (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 153 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 181 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  18 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 181 (accept_3_3 17
  153 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 181
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 153 181 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 153 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 181 (accept_3_3 14 153 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 153 181 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 153 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 181
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 181 (accept_3_3 11 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 181 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 153 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 181 (accept_3_3 8 153 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 181 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 153
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 181
  (Polychromatic418967fa.accept_11_6_10_5_1_341 6 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 181 (accept_3_3 5 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 181 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 153 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 181 (accept_3_3 2 153 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 181 (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 153 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 181))))))))))))))))))))))))))))) (allB_succ' 30 152
  181 (Eq.refl Bool.true) (allA_of_3_1 30 152 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 151 181
  (Eq.refl Bool.true) (allA_succ_of_accept 30 151 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 151 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 181 (accept_3_3 29 151 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 181 (Polychromatic418967fa.accept_16_12_7_5_1_1412 28 151
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 181
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 181 (accept_3_3 26 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 181 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 151 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 181 (accept_3_3 23 151 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 151 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 181
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 181 (accept_3_3 20 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 181 (accept_3_3 17 151 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 151 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 181
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 181 (accept_3_3 14 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 151 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 181 (accept_3_3 11 151 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 181 (accept_3_3 8 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 181 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 181 (accept_3_3 5 151 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 181 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 151 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 181 (accept_3_3 2 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 181 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 151 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 181))))))))))))))))))))))))))))))) (allB_succ' 32 150 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 150 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 150 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 150 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 150 181 (accept_3_3 29 150 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 181
  (Polychromatic418967fa.accept_27_1_15_19_1_10437 28 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 181 (accept_3_3 26 150 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 150 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 181
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 181 (accept_3_3 23 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 150 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 181 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 150 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 181 (accept_3_3 20 150 181
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  150 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 181
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 181 (accept_3_3 17 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 150 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 150 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 181 (accept_3_3 14 150 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 181 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 150 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 181
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 181 (accept_3_3 11 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 181 (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 181 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 150 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 181 (accept_3_3 8 150 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 181
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 181 (accept_3_3 5 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 181 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 150 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 181 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 181 (accept_3_3 2 150 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 181 (Polychromatic418967fa.accept_16_1_6_5_1_4385 1 150 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 181)))))))))))))))))))))))))))))))) (allB_succ' 33
  149 181 (Eq.refl Bool.true) (allA_of_3_1 33 149 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 148 181
  (Eq.refl Bool.true) (allA_succ_of_accept 33 148 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 181 (accept_3_3 32 148 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 181 (Polychromatic418967fa.accept_16_15_4_5_1_1411 31 148
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 181
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 181 (accept_3_3 29 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 181 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 181 (accept_3_3 26 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 148 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 181 (accept_3_3 23 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 181 (accept_3_3 20 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 181 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 148 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 181
  (Polychromatic418967fa.accept_15_3_13_1_1_479 18 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 181 (accept_3_3 17 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 181 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 181 (accept_3_3 14 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 181 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 148 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 181
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 181 (accept_3_3 11 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 181 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 181 (accept_3_3 8 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 181 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 148 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 181
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 181 (accept_3_3 5 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 181 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 148 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 181 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 181 (accept_3_3 2 148 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 181 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 148 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 181)))))))))))))))))))))))))))))))))) (allB_succ' 35
  147 181 (Eq.refl Bool.true) (allA_succ_of_accept 34 147 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 147 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 181 (accept_3_3 32 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 181 (accept_3_3 29 147 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 181
  (Polychromatic418967fa.accept_18_9_3_1_1_2559 27 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 181 (accept_3_3 26 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 181 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 147 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 181 (accept_3_3 23 147 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 181
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 181 (accept_3_3 20 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 181 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 181 (accept_3_3 17 147 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 181
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 181 (accept_3_3 14 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 181 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 181 (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 147 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 181 (accept_3_3 11 147 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 181
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 181 (accept_3_3 8 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 181 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 181 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 181 (accept_3_3 5 147 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 181 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 181
  (Polychromatic418967fa.accept_13_3_4_12_1_36 3 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 181 (accept_3_3 2 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 181 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 147 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 181))))))))))))))))))))))))))))))))))) (allB_succ' 36 146 181 (Eq.refl Bool.true)
  (allA_of_3_1 36 146 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 145 181 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 145 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 145 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 181 (accept_3_3 35 145 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 145 181 (Polychromatic418967fa.accept_10_4_5_1_1_497 34 145 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 181
  (Polychromatic418967fa.accept_19_14_12_10_1_3368 33 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 145 181 (accept_3_3 32 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 145 181 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 145 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 181 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 145
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 181 (accept_3_3 29 145
  181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 181
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 145 181 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 145 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 181 (accept_3_3 26 145 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 145 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 145 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 181 (Polychromatic418967fa.accept_10_4_5_1_1_497
  24 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 181 (accept_3_3 23
  145 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 181
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 145 181 (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 145 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 181 (accept_3_3 20 145 181 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 145 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 145 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 181
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 181 (accept_3_3 17 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 181 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 145 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 181 (accept_3_3 14 145 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 181 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 145 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 181
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 181 (accept_3_3 11 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 181 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 181 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 145 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 181 (accept_3_3 8 145 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 181 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 145 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 181
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 181 (accept_3_3 5 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 181 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 145 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 181 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 145 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 181 (accept_3_3 2 145 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 181 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 181)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 144 181 (Eq.refl Bool.true) (allA_succ_of_accept 37 144 181 (Polychromatic418967fa.accept_7_2_4_6_1_166
  37 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 144 181
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 144 181 (accept_3_3 35 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 144 181 (Polychromatic418967fa.accept_13_8_1_12_1_762 34 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 144 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 144 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 181 (accept_3_3 32 144 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 144 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 181
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 144 181 (accept_3_3 29 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 144 181 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 144 181 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 144 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 181 (accept_3_3 26 144 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 144
  181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 181
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 144 181 (accept_3_3 23 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 144 181 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 144 181 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 144 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 181 (accept_3_3 20 144 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 181 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 144 181
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 181
  (Polychromatic418967fa.accept_13_5_1_12_1_740 18 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 144 181 (accept_3_3 17 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 144 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 144 181 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 144 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 181 (accept_3_3 14 144 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 181 (Polychromatic418967fa.accept_23_13_6_20_1_10436 13
  144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 181
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 144 181 (accept_3_3 11 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 144 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 144 181 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 181 (accept_3_3 8 144 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 181 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 144 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 181
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 144 181 (accept_3_3 5 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  144 181 (Polychromatic418967fa.accept_21_4_18_13_1_10435 4 144 181 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 144 181 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 144 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 181 (accept_3_3 2 144 181 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 181 (Polychromatic418967fa.accept_17_1_8_11_1_6471 1 144 181 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 181))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_181_segment_000)))))))))))))))))))))))))))))))))))))


