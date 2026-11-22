-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch197
-- name    : Polychromatic418967fa_Branch197
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:21:24.715768+00:00
-- url     : https://prove2.me/theorems/b41291d1-332a-43a5-91d0-9db6c034be6f
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch197_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_197 : allB 197 197 :=
  allB_succ' 2 196 197 (Eq.refl Bool.true) (allA_of_3_0 2 196 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  195 197 (Eq.refl Bool.true) (allA_succ_of_accept 2 195 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 197 (accept_3_2 1 195 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195 197))) (allB_succ' 4 194 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 194 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 194 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 194 197 (accept_3_2 1 194 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 197)))) (allB_succ' 5 193 197 (Eq.refl Bool.true) (allA_of_3_0
  5 193 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 192 197 (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 192 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 192 197 (accept_3_2 4 192 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 192 197 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 192 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 192 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 197 (accept_3_2 1 192 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 197)))))) (allB_succ' 7 191 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 191 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 191 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 191 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 197 (accept_3_2 4 191 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  191 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 197 (accept_3_2 1 191 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191 197)))))))
  (allB_succ' 8 190 197 (Eq.refl Bool.true) (allA_of_3_0 8 190 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 189 197 (Eq.refl Bool.true) (allA_succ_of_accept 8 189 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 197 (accept_3_2 7 189 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 197 (Polychromatic418967fa.accept_14_6_7_1_1_78 6
  189 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 197
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 189 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 197 (accept_3_2 4 189 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 197 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 189 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 189 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 197 (accept_3_2 1 189 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 189 197))))))))) (allB_succ' 10 188 197 (Eq.refl Bool.true) (allA_succ_of_accept 9 188
  197 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 188 197 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 188 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 197 (accept_3_2 7 188 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 188 197 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 188 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 188 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 5
  188 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 197 (accept_3_2 4 188
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 188 197 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 188 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 197
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 188 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 188 197 (accept_3_2 1 188 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  197)))))))))) (allB_succ' 11 187 197 (Eq.refl Bool.true) (allA_of_3_0 11 187 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 186 197 (Eq.refl Bool.true) (allA_succ_of_accept 11 186 197
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 186 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 186 197 (accept_3_2 10 186 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  186 197 (Polychromatic418967fa.accept_17_9_16_10_1_362 9 186 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 186 197 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 186 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 197 (accept_3_2 7 186 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 197 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 186 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 186 197
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 186 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 186 197 (accept_3_2 4 186 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  186 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 186 197 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 186 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 197 (accept_3_2 1 186 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 186 197)))))))))))) (allB_succ' 13 185 197 (Eq.refl Bool.true) (allA_succ_of_accept 12
  185 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 185 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 197 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 185 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 197 (accept_3_2 10 185 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 185 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 197
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 185 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 197 (accept_3_2 7 185 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 185 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 185 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 197 (accept_3_2 4 185 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 185 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 197
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 185 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 197 (accept_3_2 1 185 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  197))))))))))))) (allB_succ' 14 184 197 (Eq.refl Bool.true) (allA_of_3_0 14 184 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 183 197 (Eq.refl Bool.true) (allA_succ_of_accept 14 183 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 183 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 197 (accept_3_2 13 183 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 183 197 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 183 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 183 197 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 183 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 197 (accept_3_2 10 183 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 183 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 197
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 197 (accept_3_2 7 183 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  183 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 183 197 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 183 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 197 (accept_3_2 4 183 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 197 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 183 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 197 (accept_3_2 1 183 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  197))))))))))))))) (allB_succ' 16 182 197 (Eq.refl Bool.true) (allA_succ_of_accept 15 182 197
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 182 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 182 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 182 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 182 197 (accept_3_2 13 182 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 182 197 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 182 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 182 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  182 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 197 (accept_3_2 10
  182 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 197
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 182 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 182 197 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 182 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 182 197 (accept_3_2 7 182 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 182 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 182 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  182 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 197 (accept_3_2 4 182
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 197 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 182 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 197
  (Polychromatic418967fa.accept_17_2_12_10_1_9034 2 182 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 197 (accept_3_2 1 182 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  197)))))))))))))))) (allB_succ' 17 181 197 (Eq.refl Bool.true) (allA_of_3_0 17 181 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 180 197 (Eq.refl Bool.true) (allA_succ_of_accept 17 180 197
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 180 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 180 197 (accept_3_2 16 180 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 180 197 (Polychromatic418967fa.accept_16_15_4_5_1_1411 15 180 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 180 197 (Polychromatic418967fa.accept_21_14_12_8_1_6833 14 180 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 197 (accept_3_2 13 180 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 197 (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 180
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 197
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 180 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 180 197 (accept_3_2 10 180 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  180 197 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 180 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 180 197 (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 180 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 197 (accept_3_2 7 180 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 197 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 180 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 197
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 180 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 180 197 (accept_3_2 4 180 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  180 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 180 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 180 197 (Polychromatic418967fa.accept_19_2_9_7_1_11483 2 180 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 197 (accept_3_2 1 180 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 197)))))))))))))))))) (allB_succ' 19 179 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 179 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 179 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 179 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 197 (accept_3_2 16 179 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 197
  (Polychromatic418967fa.accept_19_15_8_7_1_11482 15 179 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 179 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 197 (accept_3_2 13 179 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 179 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 197
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 179 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 179 197 (accept_3_2 10 179 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 179 197 (Polychromatic418967fa.accept_19_9_8_7_1_2061 9 179 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 197 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 179 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 197 (accept_3_2 7 179 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  179 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 197
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 179 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 197 (accept_3_2 4 179 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 179 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 179 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 197 (accept_3_2 1 179 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 197))))))))))))))))))) (allB_succ' 20 178 197 (Eq.refl Bool.true) (allA_of_3_0 20
  178 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 177 197 (Eq.refl Bool.true) (allA_succ_of_accept 20
  177 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 177 197 (accept_3_2 19 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 177 197 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 177 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 177 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 197 (accept_3_2 16 177 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 197 (Polychromatic418967fa.accept_12_3_9_5_1_853
  15 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 197
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 197 (accept_3_2 13 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 177 197 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 177 197 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 177 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 197 (accept_3_2 10 177 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 197 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 177 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 197
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 197 (accept_3_2 7 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  177 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 177 197 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 177 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 197 (accept_3_2 4 177 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 177 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 197
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 197 (accept_3_2 1 177 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  197))))))))))))))))))))) (allB_succ' 22 176 197 (Eq.refl Bool.true) (allA_succ_of_accept 21 176 197
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 176 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 176 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 176 197 (accept_3_2 19 176 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 176 197 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 176 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 176 197
  (Polychromatic418967fa.accept_19_17_5_7_1_5896 17 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 176 197 (accept_3_2 16 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 176 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 176 197 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 176 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 197 (accept_3_2 13 176 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 176 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 176 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 176 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 176 197 (accept_3_2 10 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  176 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 176 197 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 176 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 197 (accept_3_2 7 176 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 176 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 176 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 176 197
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 176 197 (accept_3_2 4 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  176 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 176 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 176 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 176 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 176 197 (accept_3_2 1 176 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176 197)))))))))))))))))))))) (allB_succ' 23 175 197 (Eq.refl Bool.true) (allA_of_3_0
  23 175 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 174 197 (Eq.refl Bool.true) (allA_succ_of_accept 23
  174 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 174 197 (accept_3_2 22 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 174 197 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 174 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 174 197 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 174 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 197 (accept_3_2 19 174 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 197
  (Polychromatic418967fa.accept_24_18_6_5_1_11477 18 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 174 197 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 174 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 197 (accept_3_2 16 174 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 174 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 174 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 197
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 174 197 (accept_3_2 13 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 174 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 174 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 174 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 197 (accept_3_2 10 174 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 174 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 174 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 197
  (Polychromatic418967fa.accept_11_8_9_10_1_503 8 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 174 197 (accept_3_2 7 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  174 197 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 174 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 174 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 197 (accept_3_2 4 174 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 174 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 197
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 174 197 (accept_3_2 1 174 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  197)))))))))))))))))))))))) (allB_succ' 25 173 197 (Eq.refl Bool.true) (allA_succ_of_accept 24 173 197
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 173 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 173 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 173 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 197 (accept_3_2 22 173 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 173 197 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 173 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 197 (Polychromatic418967fa.accept_7_6_5_1_1_416
  20 173 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 197 (accept_3_2 19
  173 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 197
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 173 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 173 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 173 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 197 (accept_3_2 16 173 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 173 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 173 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 197 (Polychromatic418967fa.accept_9_5_2_8_1_109
  14 173 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 197 (accept_3_2 13
  173 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 197
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 173 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 173 197 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 173 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 197 (accept_3_2 10 173 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 173 197 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 173 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 197 (Polychromatic418967fa.accept_16_8_13_5_1_1395
  8 173 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 197 (accept_3_2 7
  173 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 197
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 173 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 173 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 197 (accept_3_2 4 173 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 173 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 173 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 197 (Polychromatic418967fa.accept_16_2_13_5_1_2257
  2 173 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 197 (accept_3_2 1
  173 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173 197))))))))))))))))))))))))) (allB_succ' 26 172 197
  (Eq.refl Bool.true) (allA_of_3_0 26 172 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 171 197 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 171 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 197 (accept_3_2 25 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 197 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 171 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 197
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 197 (accept_3_2 22 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 197 (accept_3_2 19 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 171 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 197
  (Polychromatic418967fa.accept_21_17_3_8_1_6793 17 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 197 (accept_3_2 16 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 197 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 197 (accept_3_2 13 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 171 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 197
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 197 (accept_3_2 10 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 197 (accept_3_2 7 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 171 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 197
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 197 (accept_3_2 4 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 197 (Polychromatic418967fa.accept_23_3_10_13_1_11481 3 171 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 197 (accept_3_2 1 171 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 197))))))))))))))))))))))))))) (allB_succ' 28 170 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 170 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 170 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 197 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 170
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 170 197 (accept_3_2 25 170
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 170 197
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 170 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 170 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 197 (accept_3_2 22 170 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 170 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 170 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 170 197 (Polychromatic418967fa.accept_7_6_2_1_1_214
  20 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 170 197 (accept_3_2 19
  170 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 197
  (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 170 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 170 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 197 (accept_3_2 16 170 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 170 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 170 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 197
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 170 197 (accept_3_2 13 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 170 197 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 170 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 170 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 197 (accept_3_2 10 170 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 170 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 170 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 197
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 170 197 (accept_3_2 7 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  170 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 170 197 (Polychromatic418967fa.accept_18_5_8_17_1_3478 5 170 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 197 (accept_3_2 4 170 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 197
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 197 (accept_3_2 1 170 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  197)))))))))))))))))))))))))))) (allB_succ' 29 169 197 (Eq.refl Bool.true) (allA_of_3_0 29 169 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 168 197 (Eq.refl Bool.true) (allA_succ_of_accept 29 168 197
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 168 197 (accept_3_2 28 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 168 197 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 168 197 (Polychromatic418967fa.accept_22_4_14_21_1_11480 26 168 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 197 (accept_3_2 25 168 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 197 (Polychromatic418967fa.accept_22_2_14_21_1_2101 24 168
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 168 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 197 (accept_3_2 22 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 168 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 168 197 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 168 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 197 (accept_3_2 19 168 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 197 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 168 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 197
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 197 (accept_3_2 16 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 168 197 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 168 197 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 168 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 197 (accept_3_2 13 168 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 168 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 197
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 197 (accept_3_2 10 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  168 197 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 168 197 (Polychromatic418967fa.accept_17_8_15_10_1_10367 8 168 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 197 (accept_3_2 7 168 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 197 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 168
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 197 (accept_3_2 4 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  168 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 168 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 168 197 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 168 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 197 (accept_3_2 1 168 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 168 197)))))))))))))))))))))))))))))) (allB_succ' 31 167 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 167 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 167 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 167 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 197 (accept_3_2 28 167 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 197
  (Polychromatic418967fa.accept_16_11_7_5_1_4364 27 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 167 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 167 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 197 (accept_3_2 25 167 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 167 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 167 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 23
  167 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 197 (accept_3_2 22
  167 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 197
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 167 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 167 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 197 (accept_3_2 19 167 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 167 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 167 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 197
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 197 (accept_3_2 16 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 167 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 197 (accept_3_2 13 167 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 167 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 197 (accept_3_2 10 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 197 (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 167 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 197 (accept_3_2 7 167 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 197
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 197 (accept_3_2 4 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 167 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 197 (accept_3_2 1 167 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 197))))))))))))))))))))))))))))))) (allB_succ' 32 166 197 (Eq.refl Bool.true)
  (allA_of_3_0 32 166 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 165 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 165 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 165 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 197 (accept_3_2 31 165 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 165 197 (Polychromatic418967fa.accept_19_11_13_7_1_5862 30 165 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 197
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 197 (accept_3_2 28 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 197 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 197 (accept_3_2 25 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 165 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 197
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 197 (accept_3_2 22 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 197 (Polychromatic418967fa.accept_19_2_13_7_1_7211 21 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 165 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 197 (accept_3_2 19 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 197 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 165 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 197
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 197 (accept_3_2 16 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 197 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 197 (accept_3_2 13 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 165 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 197
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 197 (accept_3_2 10 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  165 197 (Polychromatic418967fa.accept_19_9_13_7_1_5830 9 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 197 (accept_3_2 7 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 197 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 165 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 197
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 197 (accept_3_2 4 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 165 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 197 (accept_3_2 1 165 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 197))))))))))))))))))))))))))))))))) (allB_succ' 34 164 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 164 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 164 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 164 197 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 164 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 164 197 (accept_3_2 31 164 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 164 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 30
  164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 164 197
  (Polychromatic418967fa.accept_18_11_2_17_1_3490 29 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 164 197 (accept_3_2 28 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 164 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 164 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 164 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 164 197 (accept_3_2 25 164 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 164 197 (Polychromatic418967fa.accept_9_6_2_8_1_592
  24 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 164 197
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 164 197 (accept_3_2 22 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 164 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 164 197 (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 164 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 164 197 (accept_3_2 19 164 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 164 197 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 164 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 164 197
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 164 197 (accept_3_2 16 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 164 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 164 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 164 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 197 (accept_3_2 13 164 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 164 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 164 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 197
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 164 197 (accept_3_2 10 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  164 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 164 197 (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 164 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 197 (accept_3_2 7 164 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 164 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 164 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 197
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 164 197 (accept_3_2 4 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  164 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 164 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 164 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 197 (accept_3_2 1 164 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 197)))))))))))))))))))))))))))))))))) (allB_succ' 35 163 197 (Eq.refl Bool.true)
  (allA_of_3_0 35 163 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 162 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 162 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 162 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 162 197 (accept_3_2 34 162 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 162 197 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 162 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 197
  (Polychromatic418967fa.accept_20_12_2_17_1_1620 32 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 162 197 (accept_3_2 31 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 162 197 (Polychromatic418967fa.accept_13_4_6_2_1_1437 30 162 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 162 197 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 162
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 197 (accept_3_2 28 162
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 162 197
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 162 197 (Polychromatic418967fa.accept_21_5_15_8_1_9935 26 162 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 197 (accept_3_2 25 162 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 162 197 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 162 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 197
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 197 (accept_3_2 22 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 162 197 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 162 197 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 162 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 197 (accept_3_2 19 162 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 197 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 162
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 197
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 197 (accept_3_2 16 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 162 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 162 197 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 162 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 197 (accept_3_2 13 162 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 197 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 162
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 162 197
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 197 (accept_3_2 10 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  162 197 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 162 197 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 162 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 197 (accept_3_2 7 162 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 197 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 162 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 197
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 197 (accept_3_2 4 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  162 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 162 197 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 162 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 197 (accept_3_2 1 162 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 162 197)))))))))))))))))))))))))))))))))))) (allB_succ' 37 161 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 161 197 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 161 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 197 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 161
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 197 (accept_3_2 34 161
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 197
  (Polychromatic418967fa.accept_13_7_5_2_1_401 33 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 161 197 (Polychromatic418967fa.accept_17_15_8_10_1_2886 32 161 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 197 (accept_3_2 31 161 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 197 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 161 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 197
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 197 (accept_3_2 28 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 197 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 197 (Polychromatic418967fa.accept_10_6_1_7_1_342 26 161 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 197 (accept_3_2 25 161 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 197 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 161
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 197
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 197 (accept_3_2 22 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 197 (Polychromatic418967fa.accept_15_6_11_2_1_2801 21 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 161 197 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 161 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 197 (accept_3_2 19 161 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 197 (Polychromatic418967fa.accept_20_18_1_17_1_4085 18 161 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 197
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 197 (accept_3_2 16 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 197 (Polychromatic418967fa.accept_16_15_1_5_1_2265 15 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 197 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 161 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 197 (accept_3_2 13 161 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 197 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 161 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 197
  (Polychromatic418967fa.accept_19_11_9_7_1_4447 11 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 197 (accept_3_2 10 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 197 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 197 (Polychromatic418967fa.accept_14_8_7_1_1_1615 8 161 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 197 (accept_3_2 7 161 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 197 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 161 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 197
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 197 (accept_3_2 4 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 197 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 161 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 197 (Polychromatic418967fa.accept_17_2_8_10_1_2870 2 161 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 197 (accept_3_2 1 161 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 161 197))))))))))))))))))))))))))))))))))))) (allB_succ' 38 160 197 (Eq.refl
  Bool.true) (allA_of_3_0 38 160 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 159 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 159 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 159 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 197 (accept_3_2 37 159 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 159 197 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 159 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 197
  (Polychromatic418967fa.accept_13_9_3_2_1_399 35 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 197 (accept_3_2 34 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 197 (accept_3_2 31 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 159 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 197
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 197 (accept_3_2 28 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 197 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 197 (accept_3_2 25 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 159 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 197 (accept_3_2 22 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 197 (accept_3_2 19 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 197
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 197 (accept_3_2 16 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 197 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 197 (accept_3_2 13 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 159 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 197
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 197 (accept_3_2 10 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 197 (accept_3_2 7 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 197 (accept_3_2 4 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 159 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 197 (accept_3_2 1 159 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 197))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 158 197 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 158 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 158 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 158 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 38
  158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 158 197 (accept_3_2 37
  158 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 158 197
  (Polychromatic418967fa.accept_15_6_8_2_1_104 36 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 158 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 158 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 197 (accept_3_2 34 158 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 158 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 158 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 197 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 158 197 (accept_3_2 31
  158 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 158 197
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 158 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 158 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 197 (accept_3_2 28 158 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 158 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 158 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 197 (Polychromatic418967fa.accept_7_5_4_1_1_412
  26 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 197 (accept_3_2 25
  158 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 158 197
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 158 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 158 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 197 (accept_3_2 22 158 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 158 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 158 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 197 (accept_3_2 19
  158 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 197
  (Polychromatic418967fa.accept_19_18_6_7_1_5882 18 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 158 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 158 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 197 (accept_3_2 16 158 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 158 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 197
  (Polychromatic418967fa.accept_17_14_5_10_1_9052 14 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 158 197 (accept_3_2 13 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 158 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 158 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 197 (accept_3_2 10 158 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 9
  158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 197
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 197 (accept_3_2 7 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 158 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 197 (accept_3_2 4 158 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 197 (accept_3_2 1 158 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  197)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 157 197 (Eq.refl Bool.true) (allA_of_3_0 41 157 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 156 197 (Eq.refl Bool.true) (allA_succ_of_accept 41 156 197
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 156 197 (accept_3_2 40 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 156 197 (Polychromatic418967fa.accept_16_7_12_5_1_734 39 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 156 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 197 (accept_3_2 37 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 197 (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 156 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 156 197
  (Polychromatic418967fa.accept_19_16_4_7_1_5879 35 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 156 197 (accept_3_2 34 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 156 197 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 156 197 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 197 (accept_3_2 31 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 197 (Polychromatic418967fa.accept_17_13_3_10_1_5157 30 156 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 156 197
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 197 (accept_3_2 28 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 156 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 156 197 (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 156 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 197 (accept_3_2 25 156 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 156 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 197
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 156 197 (accept_3_2 22 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 156 197 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 156 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 197 (accept_3_2 19 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 197 (Polychromatic418967fa.accept_21_18_9_8_1_11479 18 156 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 197
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 156 197 (accept_3_2 16 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 156 197 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 156 197 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 197 (accept_3_2 13 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 197 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 156 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 197
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 197 (accept_3_2 10 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  156 197 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 156 197 (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 197 (accept_3_2 7 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 156 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 197
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 197 (accept_3_2 4 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  156 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 156 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 156 197 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 197 (accept_3_2 1 156 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 156 197)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 155 197 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 155 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 197 (Polychromatic418967fa.accept_9_5_2_8_1_109
  41 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 197 (accept_3_2 40
  155 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 197
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 155 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 155 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 197 (accept_3_2 37 155 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 155 197 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 155 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 197
  (Polychromatic418967fa.accept_11_2_1_10_1_196 35 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 197 (accept_3_2 34 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 197 (accept_3_2 31 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 155 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 197
  (Polychromatic418967fa.accept_13_3_12_2_1_385 29 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 197 (accept_3_2 28 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 197 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 197 (accept_3_2 25 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 155 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 197
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 197 (accept_3_2 22 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 197 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 197 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 155 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 197 (accept_3_2 19 155 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 155 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 197
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 197 (accept_3_2 16 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 197 (accept_3_2 13 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 197 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 155 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 197
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 197 (accept_3_2 10 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 197 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 197 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 197 (accept_3_2 7 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 155 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 197
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 197 (accept_3_2 4 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 197 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 155 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 197 (accept_3_2 1 155 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 197))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 154 197 (Eq.refl
  Bool.true) (allA_of_3_0 44 154 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 153 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 153 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 153 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 197 (accept_3_2 43 153 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 153 197 (Polychromatic418967fa.accept_13_3_10_2_1_381 42 153 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 197
  (Polychromatic418967fa.accept_24_17_9_5_1_7985 41 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 197 (accept_3_2 40 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 197 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 197 (accept_3_2 37 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 197 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 153 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 197
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 197 (accept_3_2 34 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 153 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 197 (accept_3_2 31 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 153 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 197
  (Polychromatic418967fa.accept_13_3_10_2_1_381 29 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 197 (accept_3_2 28 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 197 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 197 (accept_3_2 25 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 197 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 153 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 197
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 197 (accept_3_2 22 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 197 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 197 (accept_3_2 19 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 197 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 153 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 197
  (Polychromatic418967fa.accept_16_1_9_5_1_5443 17 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 197 (accept_3_2 16 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 197 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 197 (accept_3_2 13 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 153 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 197
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 153 197 (accept_3_2 10 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 153 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 153 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 197 (accept_3_2 7 153 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 197 (Polychromatic418967fa.accept_10_6_3_7_1_2197
  6 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 197
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 197 (accept_3_2 4 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 197 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 153 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 197 (accept_3_2 1 153 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 197))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 152 197 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 152 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 152 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 197 (Polychromatic418967fa.accept_10_4_2_7_1_373
  44 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 152 197 (accept_3_2 43
  152 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 152 197
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 152 197 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 197 (accept_3_2 40 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 152 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 152 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 152 197 (accept_3_2 37
  152 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 152 197
  (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 152 197 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 197 (accept_3_2 34 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 152 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 197 (Polychromatic418967fa.accept_7_4_5_1_1_418
  32 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 152 197 (accept_3_2 31
  152 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 152 197
  (Polychromatic418967fa.accept_11_8_9_10_1_503 30 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 152 197 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 197 (accept_3_2 28 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 152 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 197 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 152 197 (accept_3_2 25
  152 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 152 197
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 152 197 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 197 (accept_3_2 22 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 152 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 197 (Polychromatic418967fa.accept_7_6_5_1_1_416
  20 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 197 (accept_3_2 19
  152 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 152 197
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 152 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 197 (accept_3_2 16 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 152 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 197 (Polychromatic418967fa.accept_10_4_2_7_1_373
  14 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 197 (accept_3_2 13
  152 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 152 197
  (Polychromatic418967fa.accept_11_1_9_10_1_184 12 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 152 197 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 197 (accept_3_2 10 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 152 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 197 (Polychromatic418967fa.accept_11_8_9_10_1_503
  8 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 197 (accept_3_2 7
  152 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 197
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 152 197 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 197 (accept_3_2 4 152 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 152 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 197 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  152 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 197 (accept_3_2 1 152
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 197))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 151 197 (Eq.refl Bool.true) (allA_of_3_0 47 151 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 48 150 197 (Eq.refl Bool.true) (allA_succ_of_accept 47 150 197 (Polychromatic418967fa.accept_4_3_2_1_1_50
  47 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 197 (accept_3_2 46
  150 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 150 197
  (Polychromatic418967fa.accept_20_5_10_17_1_11478 45 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 150 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 197 (accept_3_2 43 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 197 (Polychromatic418967fa.accept_24_18_6_5_1_11477 42 150 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 150 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 150 197 (accept_3_2 40 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 150 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 150 197 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 197 (accept_3_2 37 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 197 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 150 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 150 197
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 150 197 (accept_3_2 34 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 150 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 150 197 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 197 (accept_3_2 31 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 150 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 150 197
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 150 197 (accept_3_2 28 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 150 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 150 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 197 (accept_3_2 25 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 197 (Polychromatic418967fa.accept_17_7_14_10_1_1846 24 150 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 150 197
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 197 (accept_3_2 22 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 150 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 150 197 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 197 (accept_3_2 19 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 197 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 150 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 150 197
  (Polychromatic418967fa.accept_16_1_6_5_1_4385 17 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 150 197 (accept_3_2 16 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 150 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 150 197 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 197 (accept_3_2 13 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 150 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 150 197
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 150 197 (accept_3_2 10 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  150 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 150 197 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 197 (accept_3_2 7 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 197 (Polychromatic418967fa.accept_21_6_3_8_1_9928 6 150 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 150 197
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 197 (accept_3_2 4 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  150 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 150 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 197 (accept_3_2 1 150 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 150 197)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 149 197 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 149 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 149 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 47
  149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 197 (accept_3_2 46
  149 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 197
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 149 197 (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 149 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 197 (accept_3_2 43 149 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 149 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 149 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 197 (Polychromatic418967fa.accept_7_6_2_1_1_214
  41 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 197 (accept_3_2 40
  149 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 197
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 149 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 149 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 197 (accept_3_2 37 149 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 149 197 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 149 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 197
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 197 (accept_3_2 34 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 197 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 149 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 197 (accept_3_2 31 149 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 149 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 197 (accept_3_2 28 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 197 (Polychromatic418967fa.accept_17_9_13_10_1_1825 26 149 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 197 (accept_3_2 25 149 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 149 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 197
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 197 (accept_3_2 22 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 149 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 197 (accept_3_2 19 149 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 197 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 149 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 197
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 197 (accept_3_2 16 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 197 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 149 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 197 (accept_3_2 13 149 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 149 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 197 (accept_3_2 10 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 197 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 197 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 149 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 197 (accept_3_2 7 149 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 149 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 197
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 197 (accept_3_2 4 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 149 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 197 (accept_3_2 1 149 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 197))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 148 197
  (Eq.refl Bool.true) (allA_of_3_0 50 148 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 147 197 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 147 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 197 (accept_3_2 49 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 197 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 147 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 197
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 197 (accept_3_2 46 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 197 (accept_3_2 43 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 147 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 197
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 197 (accept_3_2 40 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 197 (Polychromatic418967fa.accept_20_19_7_17_1_7030 39 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 197 (accept_3_2 37 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 197 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 147 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 197
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 197 (accept_3_2 34 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 197 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 197 (accept_3_2 31 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 197
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 197 (accept_3_2 28 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 197 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 197 (accept_3_2 25 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 197 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 197
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 197 (accept_3_2 22 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 197 (accept_3_2 19 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 197
  (Polychromatic418967fa.accept_27_17_12_8_1_3475 17 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 147 197 (accept_3_2 16 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 147 197 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 147 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 147 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 197 (accept_3_2 13 147 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 197
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 197 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 147 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 197 (accept_3_2 10 147 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 8
  147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 197 (accept_3_2 7 147
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 197 (Polychromatic418967fa.accept_4_2_3_1_1_2
  6 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 197
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 197 (accept_3_2 4 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 197 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 147 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 197 (accept_3_2 1 147 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 197))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 146 197
  (Eq.refl Bool.true) (allA_succ_of_accept 51 146 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 146 197
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 146 197 (accept_3_2 49 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 146 197 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 146 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 197 (accept_3_2 46 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 197
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 197 (accept_3_2 43 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 146 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 197 (accept_3_2 40 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 197
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 38 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 146 197 (accept_3_2 37 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 146 197 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 146 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 197 (accept_3_2 34 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 197
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 197 (accept_3_2 31 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 197 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 197 (accept_3_2 28 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 146 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 197
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 197 (accept_3_2 25 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 197 (accept_3_2 22 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 197
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 197 (accept_3_2 19 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 197 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 146 197 (Polychromatic418967fa.accept_19_17_13_7_1_5861 17 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 197 (accept_3_2 16 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 197
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 146 197 (accept_3_2 13 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 146 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 146 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 197 (accept_3_2 10 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 197
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 197 (accept_3_2 7 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 197 (accept_3_2 4 146 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 197
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 197 (accept_3_2 1 146 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  197)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 145 197 (Eq.refl Bool.true) (allA_of_3_0 53 145
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 144 197 (Eq.refl Bool.true) (allA_succ_of_accept 53 144
  197 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 144 197 (accept_3_2 52 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 144 197 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 144 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 197 (Polychromatic418967fa.accept_19_12_11_7_1_5837 50 144
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 197 (accept_3_2 49 144
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 144 197
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 144 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 144 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 197 (accept_3_2 46 144 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 144 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 144 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 197
  (Polychromatic418967fa.accept_23_21_6_13_1_11476 44 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 144 197 (accept_3_2 43 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 144 197 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 144 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 144 197 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 144
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 197 (accept_3_2 40 144
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 197
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 39 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 144 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 144 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 197 (accept_3_2 37 144 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 144 197 (Polychromatic418967fa.accept_17_2_8_10_1_2870 36 144 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 197
  (Polychromatic418967fa.accept_11_2_1_10_1_196 35 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 144 197 (accept_3_2 34 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 144 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 144 197 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 144 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 197 (accept_3_2 31 144 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 197 (Polychromatic418967fa.accept_21_9_18_8_1_11475 30 144
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 197
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 144 197 (accept_3_2 28 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 144 197 (Polychromatic418967fa.accept_19_8_11_7_1_11474 27 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 144 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 144 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 197 (accept_3_2 25 144 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 144 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 197
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 144 197 (accept_3_2 22 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 144 197 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 144 197 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 144 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 197 (accept_3_2 19 144 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 197 (Polychromatic418967fa.accept_19_18_11_7_1_11473 18
  144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 197
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 144 197 (accept_3_2 16 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 144 197 (Polychromatic418967fa.accept_17_15_8_10_1_2886 15 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 144 197 (Polychromatic418967fa.accept_19_14_11_7_1_7236 14 144 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 197 (accept_3_2 13 144 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 144 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 197
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 197 (accept_3_2 10 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  144 197 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 144 197 (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 144 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 197 (accept_3_2 7 144 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 197 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 144 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 197
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 197 (accept_3_2 4 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  144 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 144 197 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 144 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 197 (accept_3_2 1 144 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 144 197)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 143 197
  (Eq.refl Bool.true) (allA_succ_of_accept 54 143 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 143 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 197
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 197 (accept_3_2 52 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 197 (accept_3_2 49 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 197 (Polychromatic418967fa.accept_17_14_7_10_1_7808 48 143 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 197
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 197 (accept_3_2 46 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 197 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 197 (accept_3_2 43 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 143 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 197
  (Polychromatic418967fa.accept_19_3_10_7_1_5884 41 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 197 (accept_3_2 40 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 197 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 197 (accept_3_2 37 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 197 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 143 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 197
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 197 (accept_3_2 34 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 197 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 197 (accept_3_2 31 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 143 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 197
  (Polychromatic418967fa.accept_22_7_11_21_1_2095 29 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 143 197 (accept_3_2 28 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 143 197 (Polychromatic418967fa.accept_25_2_18_22_1_11472 27 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 26
  143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 197 (accept_3_2 25
  143 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 197
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 143 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 143 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 197 (accept_3_2 22 143 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 143 197 (Polychromatic418967fa.accept_15_6_8_2_1_104 21 143 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 197
  (Polychromatic418967fa.accept_16_4_15_5_1_5537 20 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 197 (accept_3_2 19 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 197 (Polychromatic418967fa.accept_16_1_15_5_1_708 17 143 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 197 (accept_3_2 16 143 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 197 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 143
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 197 (accept_3_2 13 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 197 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 197 (accept_3_2 10 143 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 197 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 143 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 197
  (Polychromatic418967fa.accept_22_8_11_21_1_11471 8 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 143 197 (accept_3_2 7 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 143 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 143 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 197 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 143 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 197 (accept_3_2 4 143 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 197 (Polychromatic418967fa.accept_17_3_7_10_1_3948
  3 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 197 (accept_3_2 1 143 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  197))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 142 197 (Eq.refl Bool.true) (allA_of_3_0 56
  142 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 141 197 (Eq.refl Bool.true) (allA_succ_of_accept 56
  141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 141 197 (accept_3_2 55 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 141 197 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 141 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 197 (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 141
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 197 (accept_3_2 52 141
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 197
  (Polychromatic418967fa.accept_12_3_9_5_1_853 51 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 141 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 197 (accept_3_2 49 141 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 197 (Polychromatic418967fa.accept_9_2_6_8_1_321
  47 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 197 (accept_3_2 46
  141 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 197
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 197 (accept_3_2 43 141 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 197 (Polychromatic418967fa.accept_13_3_11_2_1_1422 42 141 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 197 (accept_3_2 40 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 197 (accept_3_2 37 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 197 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 141 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 197
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 197 (accept_3_2 34 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 197 (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 197 (accept_3_2 31 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 141 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 197
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 197 (accept_3_2 28 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 197 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 197 (accept_3_2 25 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 197 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 141 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 197 (accept_3_2 22 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 197 (accept_3_2 19 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 197 (Polychromatic418967fa.accept_16_2_13_5_1_2257 18 141 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 197
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 197 (accept_3_2 16 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 197 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 197 (accept_3_2 13 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 141 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 197
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 197 (accept_3_2 10 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 197 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 197 (accept_3_2 7 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 197 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 141 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 197 (accept_3_2 4 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 141 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 197 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 197 (accept_3_2 1 141 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 197))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 140 197
  (Eq.refl Bool.true) (allA_succ_of_accept 57 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 140 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 140 197 (accept_3_2 55 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 140 197 (Polychromatic418967fa.accept_21_12_14_8_1_5258 54 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 140 197 (Polychromatic418967fa.accept_11_9_8_10_1_934 53 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 197 (accept_3_2 52 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 140 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 140 197
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 140 197 (accept_3_2 49 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 140 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 140 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 197 (accept_3_2 46 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 140 197
  (Polychromatic418967fa.accept_13_5_10_2_1_856 44 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 197 (accept_3_2 43 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 140 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 140 197 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 140 197 (accept_3_2 40 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 140 197 (accept_3_2 37 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 140 197 (Polychromatic418967fa.accept_16_4_12_5_1_2287 36 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 140 197 (Polychromatic418967fa.accept_22_13_8_21_1_9872 35 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 140 197 (accept_3_2 34 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 197
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 140 197 (accept_3_2 31 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 140 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 140 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 197 (accept_3_2 28 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 197
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 140 197 (accept_3_2 25 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 140 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 197 (Polychromatic418967fa.accept_16_7_12_5_1_734 23 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 197 (accept_3_2 22 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 140 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 140 197 (accept_3_2 19 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 140 197 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 140 197 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 197 (accept_3_2 16 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 197
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 140 197 (accept_3_2 13 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 140 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 197 (accept_3_2 10 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 197
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 197 (accept_3_2 7 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 197 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 197 (accept_3_2 4 140 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 197 (accept_3_2 1 140 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  197)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 139 197 (Eq.refl Bool.true) (allA_of_3_0
  59 139 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 138 197 (Eq.refl Bool.true) (allA_succ_of_accept 59
  138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 138 197 (accept_3_2 58 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 138 197 (Polychromatic418967fa.accept_15_12_3_2_1_2756 57 138 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 197 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 138 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 197 (accept_3_2 55 138 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 197
  (Polychromatic418967fa.accept_22_10_6_21_1_8302 54 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 138 197 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 197 (accept_3_2 52 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 138 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 197
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 138 197 (accept_3_2 49 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 138 197 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 197 (accept_3_2 46 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 138 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 197
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 44 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 138 197 (accept_3_2 43 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 138 197 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 138 197 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 197 (accept_3_2 40 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 197
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 138 197 (accept_3_2 37 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 138 197 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 197 (accept_3_2 34 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 197 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 138 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 197
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 197 (accept_3_2 31 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 138 197 (Polychromatic418967fa.accept_16_14_10_5_1_1393 30 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 138 197 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 197 (accept_3_2 28 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 197
  (Polychromatic418967fa.accept_21_5_12_8_1_6807 26 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 197 (accept_3_2 25 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 138 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 197 (accept_3_2 22 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 197 (Polychromatic418967fa.accept_19_2_5_7_1_10021 21 138 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 197
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 197 (accept_3_2 19 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 138 197 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 138 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 197 (accept_3_2 16 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 197
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 197 (accept_3_2 13 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 138 197 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 197 (accept_3_2 10 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 197 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 138 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 197
  (Polychromatic418967fa.accept_17_8_2_10_1_2879 8 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 197 (accept_3_2 7 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  138 197 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 138 197 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 197 (accept_3_2 4 138 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 197
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 197 (accept_3_2 1 138 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  197)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 137 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 137 197 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 137 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 197 (accept_3_2 58 137 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 197 (Polychromatic418967fa.accept_9_3_2_8_1_108
  57 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 197
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 137 197 (accept_3_2 55 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 137 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 197 (Polychromatic418967fa.accept_27_26_2_8_1_11470 53 137
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 197 (accept_3_2 52 137
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 197
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 137 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 197 (accept_3_2 49 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 137 197 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 197 (Polychromatic418967fa.accept_7_5_4_1_1_412
  47 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 197 (accept_3_2 46
  137 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 197
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 137 197 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 197 (accept_3_2 43 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 137 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 197 (Polychromatic418967fa.accept_9_5_2_8_1_109
  41 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 197 (accept_3_2 40
  137 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 197
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 137 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 197 (accept_3_2 37 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 137 197 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 197 (Polychromatic418967fa.accept_13_9_7_2_1_3869
  35 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 197 (accept_3_2 34
  137 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 197
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 137 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 197 (accept_3_2 31 137 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 137 197 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 197
  (Polychromatic418967fa.accept_16_13_9_5_1_3302 29 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 197 (accept_3_2 28 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 197 (Polychromatic418967fa.accept_16_11_9_5_1_4412 27 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 197 (accept_3_2 25 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 137 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 197
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 197 (accept_3_2 22 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 197 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 197 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 197 (accept_3_2 19 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 197 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 137 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 197
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 197 (accept_3_2 16 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 197 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 197 (accept_3_2 13 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 197 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 197
  (Polychromatic418967fa.accept_16_11_9_5_1_4412 11 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 197 (accept_3_2 10 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 197 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 197 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 197 (accept_3_2 7 137 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 197 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 137 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 197
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 197 (accept_3_2 4 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 197 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 137 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 197 (Polychromatic418967fa.accept_18_2_11_17_1_4773 2 137 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 197 (accept_3_2 1 137 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 137 197)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 136 197 (Eq.refl Bool.true) (allA_of_3_0 62 136 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 63 135 197 (Eq.refl Bool.true) (allA_succ_of_accept 62 135 197 (Polychromatic418967fa.accept_4_2_3_1_1_2
  62 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 197 (accept_3_2 61
  135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 197
  (Polychromatic418967fa.accept_16_12_7_5_1_1412 60 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 135 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 135 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 197 (accept_3_2 58 135 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 135 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 197
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 135 197 (accept_3_2 55 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 135 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 135 197 (Polychromatic418967fa.accept_10_3_5_7_1_330 53 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 197 (accept_3_2 52 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 197 (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 135
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 197 (accept_3_2 49 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 135 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 197 (Polychromatic418967fa.accept_19_9_2_7_1_3149 47 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 197 (accept_3_2 46 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 135 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 197
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 197 (accept_3_2 43 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 135 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 197 (accept_3_2 40 135 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 197 (Polychromatic418967fa.accept_19_1_2_7_1_2054 39 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 197 (accept_3_2 37 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 197 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 197 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 197 (accept_3_2 34 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 197 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 135
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 197
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 197 (accept_3_2 31 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 197 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 197 (accept_3_2 28 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 197 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 135 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 197 (accept_3_2 25 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 197 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 197 (accept_3_2 22 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 135
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 197
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 197 (accept_3_2 19 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 135 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 197 (accept_3_2 16 135 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 197 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 135 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 197 (accept_3_2 13 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 197 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 197 (Polychromatic418967fa.accept_16_11_7_5_1_4364 11 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 197 (accept_3_2 10 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 197 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 135 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 197
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 197 (accept_3_2 7 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 197 (Polychromatic418967fa.accept_19_5_2_7_1_1019 5 135 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 197 (accept_3_2 4 135 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 197 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 197
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 197 (accept_3_2 1 135 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  197))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 134 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 134 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 134 197 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 134
  197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 134 197 (accept_3_2 61 134
  197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 134 197
  (Polychromatic418967fa.accept_25_10_9_22_1_11469 60 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 134 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 134 197 (accept_3_2 58 134 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 134 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 197
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 134 197 (accept_3_2 55 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 134 197 (Polychromatic418967fa.accept_22_10_2_21_1_11468 54 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 134 197 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 197 (accept_3_2 52 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 134 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 197
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 50 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 134 197 (accept_3_2 49 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 134 197 (Polychromatic418967fa.accept_15_3_14_2_1_1888 48 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 134 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 197 (accept_3_2 46 134 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 197
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 197 (accept_3_2 43 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 197 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 197 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 197 (accept_3_2 40 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 134 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 197
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 38 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 197 (accept_3_2 37 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 197 (Polychromatic418967fa.accept_16_4_6_5_1_2245 36 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 134 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 197 (accept_3_2 34 134 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 197
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 197 (accept_3_2 31 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 197 (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 197 (Polychromatic418967fa.accept_19_10_1_7_1_10040 29 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 197 (accept_3_2 28 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 134 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 197
  (Polychromatic418967fa.accept_22_4_2_21_1_11467 26 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 134 197 (accept_3_2 25 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 134 197 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 134 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 134 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 197 (accept_3_2 22 134 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 197
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 197 (accept_3_2 19 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 197 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 197 (Polychromatic418967fa.accept_16_1_6_5_1_4385 17 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 197 (accept_3_2 16 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 197
  (Polychromatic418967fa.accept_22_14_2_21_1_6583 14 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 134 197 (accept_3_2 13 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 134 197 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 134 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 197 (accept_3_2 10 134 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 197 (Polychromatic418967fa.accept_6_3_2_5_1_32 9
  134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 197
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 197 (accept_3_2 7 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 197 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 197 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 134 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 197 (accept_3_2 4 134 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 197 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 197
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 197 (accept_3_2 1 134 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  197)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 133 197 (Eq.refl Bool.true)
  (allA_of_3_0 65 133 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 132 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 132 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 132 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 197 (accept_3_2 64 132 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 132 197 (Polychromatic418967fa.accept_14_7_6_1_1_1656 63 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 197
  (Polychromatic418967fa.accept_20_2_12_17_1_5547 62 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 132 197 (accept_3_2 61 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 132 197 (Polychromatic418967fa.accept_16_12_4_5_1_2273 60 132 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 197 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 132 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 197 (accept_3_2 58 132 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 197 (Polychromatic418967fa.accept_8_1_4_5_1_48 57
  132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 197
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 132 197 (accept_3_2 55 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 132 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 132 197 (Polychromatic418967fa.accept_19_15_18_7_1_10018 53 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 197 (accept_3_2 52 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 132 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 132 197 (accept_3_2 49 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 132 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 132 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 197 (accept_3_2 46 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 197 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 197
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 132 197 (accept_3_2 43 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 132 197 (Polychromatic418967fa.accept_20_2_12_17_1_5547 42 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 132 197 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 197 (accept_3_2 40 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 197
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 197 (accept_3_2 37 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 132 197 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 197 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 197 (accept_3_2 34 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 132 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 197 (accept_3_2 31 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 132 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 132 197 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 197 (accept_3_2 28 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 197 (Polychromatic418967fa.accept_19_8_18_7_1_3143 27 132 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 197
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 197 (accept_3_2 25 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 197 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 197 (accept_3_2 22 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 197
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 197 (accept_3_2 19 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 197 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 197 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 197 (accept_3_2 16 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 197 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 197
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 197 (accept_3_2 13 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 197 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 197 (accept_3_2 10 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 197 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 197
  (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 197 (accept_3_2 7 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 197 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 197 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 197 (accept_3_2 4 132 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 197 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 132 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 197
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 197 (accept_3_2 1 132 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  197)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 131 197 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 131 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 131 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 197 (accept_3_2 64 131 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 197
  (Polychromatic418967fa.accept_25_13_6_22_1_11466 63 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 197 (accept_3_2 61 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 197 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 197
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 197 (accept_3_2 58 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 197 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 197 (accept_3_2 55 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 197
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 197 (accept_3_2 52 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 197 (accept_3_2 49 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 197 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 197 (accept_3_2 46 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 197 (Polychromatic418967fa.accept_10_4_1_7_1_371 44 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 197 (accept_3_2 43 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 131 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 197
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 197 (accept_3_2 40 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 197 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 197 (accept_3_2 37 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 197 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 197
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 197 (accept_3_2 34 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 197 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 197 (accept_3_2 31 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 197
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 197 (accept_3_2 28 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 197 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 197 (accept_3_2 25 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 197
  (Polychromatic418967fa.accept_17_6_12_10_1_7781 23 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 131 197 (accept_3_2 22 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 131 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 131 197 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 197 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 131 197
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 197 (accept_3_2 19 131 197
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 197
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 197 (accept_3_2 16 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 197 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 197 (accept_3_2 13 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 197 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 197
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 197 (accept_3_2 10 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 197 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 197 (Polychromatic418967fa.accept_16_8_3_5_1_5512 8 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 197 (accept_3_2 7 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 197 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 197
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 197 (accept_3_2 4 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 197 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 131 197 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 197 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 197 (accept_3_2 1 131 197 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 197)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_197_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


