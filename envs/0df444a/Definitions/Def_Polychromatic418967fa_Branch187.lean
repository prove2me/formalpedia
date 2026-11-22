-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch187
-- name    : Polychromatic418967fa_Branch187
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:19:43.695031+00:00
-- url     : https://prove2.me/theorems/582c48d0-97bd-40a4-aac2-7ac1a2da62ea
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch187_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_187 : allB 187 187 :=
  allB_succ' 2 186 187 (Eq.refl Bool.true) (allA_succ_of_accept 1 186 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  186 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 187)) (allB_succ' 3 185 187
  (Eq.refl Bool.true) (allA_of_3_1 3 185 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 184 187 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 184 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 187 (accept_3_3 2 184 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 184 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 187)))) (allB_succ' 5 183 187 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 183 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 187 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 183 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 187 (accept_3_3 2 183 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  183 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 187))))) (allB_succ' 6 182 187
  (Eq.refl Bool.true) (allA_of_3_1 6 182 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 181 187 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 181 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 181 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 187 (accept_3_3 5 181 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 187 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 181 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 187
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 181 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 187 (accept_3_3 2 181 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 187 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 181 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 187))))))) (allB_succ' 8 180 187 (Eq.refl Bool.true) (allA_succ_of_accept 7 180 187
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 180 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 180 187 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 180 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 187 (accept_3_3 5 180 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 180 187 (Polychromatic418967fa.accept_19_4_9_16_1_3811 4 180 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 187
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 180 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 180 187 (accept_3_3 2 180 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  180 187 (Polychromatic418967fa.accept_21_1_12_19_1_7721 1 180 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 180 187)))))))) (allB_succ' 9 179 187 (Eq.refl Bool.true) (allA_of_3_1 9 179 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 178 187 (Eq.refl Bool.true) (allA_succ_of_accept 9 178 187
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 187 (accept_3_3 8 178 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 187 (Polychromatic418967fa.accept_16_7_2_11_1_931 7 178 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 187 (Polychromatic418967fa.accept_15_6_13_7_1_222 6 178 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 187 (accept_3_3 5 178 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 187 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 178 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 178 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 187 (accept_3_3 2 178 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178 187)))))))))) (allB_succ' 11 177 187 (Eq.refl Bool.true) (allA_succ_of_accept 10 177 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 177 187 (Polychromatic418967fa.accept_19_9_6_16_1_5116 9 177 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 187 (accept_3_3 8 177 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 177 187 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 177 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  177 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 187 (accept_3_3 5 177
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 187 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 177 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 187
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 177 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 187 (accept_3_3 2 177 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 177 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177 187))))))))))) (allB_succ' 12 176 187 (Eq.refl Bool.true) (allA_of_3_1 12 176 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 175 187 (Eq.refl Bool.true) (allA_succ_of_accept 12 175 187
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 175 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 187 (accept_3_3 11 175 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 175 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 187 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 175 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 187 (accept_3_3 8 175 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 187 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 175 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 187
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 175 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 187 (accept_3_3 5 175 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 187 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 175 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 187 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 175 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 187 (accept_3_3 2 175 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 175 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 187))))))))))))) (allB_succ' 14 174 187 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 187 (Polychromatic418967fa.accept_10_2_4_7_1_352
  12 174 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 187 (accept_3_3 11
  174 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 187
  (Polychromatic418967fa.accept_9_1_3_7_1_6 10 174 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 174 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 187 (accept_3_3 8 174 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 174 187 (Polychromatic418967fa.accept_26_7_18_5_1_10791 7 174 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 187
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 174 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 174 187 (accept_3_3 5 174 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  174 187 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 174 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 174 187 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 174 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 187 (accept_3_3 2 174 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 187)))))))))))))) (allB_succ' 15 173 187 (Eq.refl
  Bool.true) (allA_of_3_1 15 173 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 172 187 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 172 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 172 187 (accept_3_3 14 172 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 172 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 172 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 172 187 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  172 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 187 (accept_3_3 11
  172 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 187
  (Polychromatic418967fa.accept_12_10_4_7_1_948 10 172 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 172 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 172 187 (accept_3_3 8 172 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 172 187 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 172 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 172 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  172 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 187 (accept_3_3 5 172
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 187
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 172 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 172 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 172 187 (accept_3_3 2 172 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 172 187 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 172 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 187)))))))))))))))) (allB_succ' 17 171 187 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 171 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 187 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 171 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 187 (accept_3_3 14 171 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 187
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 171 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 171 187 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 171 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 187 (accept_3_3 11 171 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 171 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 187 (Polychromatic418967fa.accept_7_2_3_5_1_34 9
  171 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 187 (accept_3_3 8 171
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 187
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 7 171 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 171 187 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 171 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 187 (accept_3_3 5 171 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 171 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 187 (Polychromatic418967fa.accept_13_3_2_5_1_1632
  3 171 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 187 (accept_3_3 2
  171 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 187
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 171 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171 187))))))))))))))))) (allB_succ' 18 170 187 (Eq.refl Bool.true) (allA_of_3_1 18 170 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 169 187 (Eq.refl Bool.true) (allA_succ_of_accept 18 169 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 187 (accept_3_3 17 169 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 187 (Polychromatic418967fa.accept_20_16_9_7_1_3402 16 169 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 187 (Polychromatic418967fa.accept_21_15_1_19_1_9205 15 169 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 187 (accept_3_3 14 169 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 187 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 169 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 187
  (Polychromatic418967fa.accept_10_2_9_7_1_720 12 169 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 187 (accept_3_3 11 169 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 187 (Polychromatic418967fa.accept_24_9_1_19_1_941 9 169 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 187 (accept_3_3 8 169 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 187 (Polychromatic418967fa.accept_19_7_17_16_1_6478 7 169 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 187 (accept_3_3 5 169 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 187 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 169 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 187 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 169 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 187 (accept_3_3 2 169 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 187 (Polychromatic418967fa.accept_19_1_17_16_1_2578 1 169 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 187))))))))))))))))))) (allB_succ' 20 168 187
  (Eq.refl Bool.true) (allA_succ_of_accept 19 168 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 168 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 187
  (Polychromatic418967fa.accept_26_18_12_5_1_10790 18 168 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 168 187 (accept_3_3 17 168 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 187 (Polychromatic418967fa.accept_23_16_7_3_1_10710 16 168 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 187 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  15 168 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 187 (accept_3_3 14
  168 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 187
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 168 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 168 187 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 168 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 187 (accept_3_3 11 168 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 168 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 168 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 187 (Polychromatic418967fa.accept_10_9_8_7_1_714 9
  168 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 187 (accept_3_3 8 168
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 187
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 168 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 168 187 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 168 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 187 (accept_3_3 5 168 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 168 187 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 168 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 187 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  168 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 187 (accept_3_3 2 168
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 187
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 168 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 187)))))))))))))))))))) (allB_succ' 21 167 187 (Eq.refl Bool.true) (allA_of_3_1 21 167 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 166 187 (Eq.refl Bool.true) (allA_succ_of_accept 21 166 187
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 166 187 (accept_3_3 20 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 166 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 166 187 (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 166 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 166 187 (accept_3_3 17 166 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 166 187 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 166
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 166 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 166 187 (accept_3_3 14 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 166 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 166 187 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 166 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 166 187 (accept_3_3 11 166 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 166 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 187
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 166 187 (accept_3_3 8 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  166 187 (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 166 187 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 166 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 187 (accept_3_3 5 166 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 187 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 166 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 166 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 166 187 (accept_3_3 2 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  166 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 166 187)))))))))))))))))))))) (allB_succ' 23 165 187 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  165 187 11 2 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 165 187 (Polychromatic418967fa.accept_19_2_13_16_1_5089 21 165 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 187 (accept_3_3 20 165 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 165 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 187 (accept_3_3 17 165 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 165 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 187 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 165 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 187 (accept_3_3 14 165 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 165 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 187
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 165 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 165 187 11 1 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 165 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 165 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 187 (Polychromatic418967fa.accept_7_2_4_5_1_313 9
  165 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 187 (accept_3_3 8 165
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 187
  (Polychromatic418967fa.accept_16_7_5_11_1_4777 7 165 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 165 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 187 (accept_3_3 5 165 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 165 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 187 (Polychromatic418967fa.accept_10_3_5_7_1_330 3
  165 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 187 (accept_3_3 2 165
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 187 (Polychromatic418967fa.accept_7_1_4_5_1_35
  1 165 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 187)))))))))))))))))))))))
  (allB_succ' 24 164 187 (Eq.refl Bool.true) (allA_of_3_1 24 164 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 25 163 187 (Eq.refl Bool.true) (allA_succ_of_accept 24 163 187 (Polychromatic418967fa.accept_7_3_2_5_1_147
  24 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 187 (accept_3_3 23
  163 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 187
  (Polychromatic418967fa.accept_9_4_1_7_1_293 22 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 163 187 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 163 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 187 (accept_3_3 20 163 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 163 187 (Polychromatic418967fa.accept_22_19_9_11_1_4271 19 163 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 187
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 187 (accept_3_3 17 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 187 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 187 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 163 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 187 (accept_3_3 14 163 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 163 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 187
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 187 (accept_3_3 11 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 187 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 187 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 163 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 187 (accept_3_3 8 163 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 187 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 163 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 187
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 187 (accept_3_3 5 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 187 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 163 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 187 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 163 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 187 (accept_3_3 2 163 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 187 (Polychromatic418967fa.accept_21_1_16_19_1_3134 1 163 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 187))))))))))))))))))))))))) (allB_succ' 26 162 187
  (Eq.refl Bool.true) (allA_succ_of_accept 25 162 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 187
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 162 187 (accept_3_3 23 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 162 187 (Polychromatic418967fa.accept_16_6_2_11_1_7132 22 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 162 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 162 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 187 (accept_3_3 20 162 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 187 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 162 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 187
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 162 187 (accept_3_3 17 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 162 187 (Polychromatic418967fa.accept_13_3_6_5_1_2336 16 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 162 187 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 162 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 187 (accept_3_3 14 162 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 187
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 187 (accept_3_3 11 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 162 187 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 162 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 187 (accept_3_3 8 162 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 187 (Polychromatic418967fa.accept_16_7_2_11_1_931 7 162 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 187
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 187 (accept_3_3 5 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 187 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 162 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 187 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 162 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 187 (accept_3_3 2 162 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 187)))))))))))))))))))))))))) (allB_succ' 27 161 187
  (Eq.refl Bool.true) (allA_of_3_1 27 161 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 160 187 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 160 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 187 (accept_3_3 26 160 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 187 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 160 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 187
  (Polychromatic418967fa.accept_19_5_8_16_1_10789 24 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 160 187 (accept_3_3 23 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 160 187 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 160 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 160 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 187 (accept_3_3 20 160 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 187 (Polychromatic418967fa.accept_13_6_4_5_1_2330
  19 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 187
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 187 (accept_3_3 17 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 187 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 187 (accept_3_3 14 160 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 187 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 160 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 187
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 187 (accept_3_3 11 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 187 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 187 (accept_3_3 8 160 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 187 (Polychromatic418967fa.accept_19_7_8_16_1_6490 7 160 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 187
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 187 (accept_3_3 5 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 187 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 160 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 187 (accept_3_3 2 160 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 187 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 160 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 187)))))))))))))))))))))))))))) (allB_succ' 29 159
  187 (Eq.refl Bool.true) (allA_succ_of_accept 28 159 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 187
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 159 187 (accept_3_3 26 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 159 187 (Polychromatic418967fa.accept_19_6_7_16_1_1418 25 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 159 187 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 159 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 187 (accept_3_3 23 159 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 159 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 187
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 187 (accept_3_3 20 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 159 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 187 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 159 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 187 (accept_3_3 17 159 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 187
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 187 (accept_3_3 14 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 159 187 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 187 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 159 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 187 (accept_3_3 11 159 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 159 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 187
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 187 (accept_3_3 8 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 187 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 187 (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 159 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 187 (accept_3_3 5 159 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 187
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 187 (accept_3_3 2 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 159 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 187))))))))))))))))))))))))))))) (allB_succ' 30 158 187 (Eq.refl Bool.true) (allA_of_3_1 30
  158 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 157 187 (Eq.refl Bool.true) (allA_succ_of_accept 30
  157 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 157 187 (accept_3_3 29 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 157 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 157 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 187 (Polychromatic418967fa.accept_19_8_5_16_1_2589 27 157
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 187 (accept_3_3 26 157
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 187
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 157 187 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 157 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 187 (accept_3_3 23 157 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 157 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 187 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 187 (accept_3_3 20
  157 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 187
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 157 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 187 (accept_3_3 17 157 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 157 187 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 157 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 187 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 187 (accept_3_3 14
  157 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 187
  (Polychromatic418967fa.accept_22_13_3_11_1_10788 13 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 187 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 157 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 187 (accept_3_3 11 157 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 187
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 187 (accept_3_3 8 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 187 (Polychromatic418967fa.accept_21_7_10_19_1_10739 7 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 187 (accept_3_3 5 157 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 187 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 157 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 187
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 187 (accept_3_3 2 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 187 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 157 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 187))))))))))))))))))))))))))))))) (allB_succ' 32 156 187 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 156 187 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 156 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 187 (Polychromatic418967fa.accept_19_11_4_16_1_9308 30 156
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 156 187 (accept_3_3 29 156
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 187 (Polychromatic418967fa.accept_9_1_3_7_1_6
  28 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 187
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 156 187 (accept_3_3 26 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 156 187 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 156 187 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 156 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 187 (accept_3_3 23 156 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 187 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 156 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 187
  (Polychromatic418967fa.accept_10_1_6_7_1_710 21 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 156 187 (accept_3_3 20 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 156 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 156 187 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 156 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 187 (accept_3_3 17 156 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 187 (Polychromatic418967fa.accept_15_1_6_7_1_6282 16 156 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 156 187
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 156 187 (accept_3_3 14 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 156 187 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 156 187 (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 156 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 187 (accept_3_3 11 156 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 187 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 156 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 156 187
  (Polychromatic418967fa.accept_19_9_4_16_1_2586 9 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 156 187 (accept_3_3 8 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  156 187 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 156 187 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 156 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 187 (accept_3_3 5 156 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 187 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 156 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 156 187
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 156 187 (accept_3_3 2 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  156 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 156 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 156 187)))))))))))))))))))))))))))))))) (allB_succ' 33 155 187 (Eq.refl Bool.true) (allA_of_3_1
  33 155 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 154 187 (Eq.refl Bool.true) (allA_succ_of_gcd 33
  154 187 11 3 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 154 187 (accept_3_3 32 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 154 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 154 187 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 154 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 187 (accept_3_3 29 154 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 154 187 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 154 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 154 187 (accept_3_3 26 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 154 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 154 187 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 154 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 187 (accept_3_3 23 154 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 154 187 11 2 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 154 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 187 (accept_3_3 20 154 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 187 (Polychromatic418967fa.accept_13_6_11_5_1_133
  19 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 187
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 187 (accept_3_3 17 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 187 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 154 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 187 (accept_3_3 14 154 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 187
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 154 187 11 1 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 154 187 (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 154 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 187
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 187 (accept_3_3 8 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  154 187 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 154 187 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 154 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 187 (accept_3_3 5 154 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 154 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 187 (accept_3_3 2 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154 187)))))))))))))))))))))))))))))))))) (allB_succ' 35 153 187 (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 153 187 17 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 153 187 (Polychromatic418967fa.accept_21_12_6_19_1_1871 33 153 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 187 (accept_3_3 32 153 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 187 (Polychromatic418967fa.accept_27_4_18_25_1_10787 31 153 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 187 (accept_3_3 29 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 187 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 153 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 187 (accept_3_3 26 153 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 187 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 153 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 187
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 153 187 (accept_3_3 23 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 153 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 153 187 (Polychromatic418967fa.accept_13_8_10_5_1_977 21 153 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 187 (accept_3_3 20 153 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 187 (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 153
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 17 153 187 17 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 16 153 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 187 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 153 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 187 (accept_3_3 14 153 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 187
  (Polychromatic418967fa.accept_19_13_1_16_1_7979 13 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 187 (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 153 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 187 (accept_3_3 11 153 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 187
  (Polychromatic418967fa.accept_25_9_3_12_1_10786 9 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 187 (accept_3_3 8 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 187 (Polychromatic418967fa.accept_22_7_21_11_1_10746 7 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 187 (accept_3_3 5 153 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 187
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 187 (accept_3_3 2 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 187 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 153 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 187))))))))))))))))))))))))))))))))))) (allB_succ' 36 152 187 (Eq.refl Bool.true)
  (allA_of_3_1 36 152 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 151 187 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 151 187 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 151 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 187 (accept_3_3 35 151 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 151 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 151 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 187
  (Polychromatic418967fa.accept_19_14_18_16_1_6530 33 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 151 187 (accept_3_3 32 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 151 187 (Polychromatic418967fa.accept_16_15_7_11_1_3760 31 151 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 187 (Polychromatic418967fa.accept_7_2_4_5_1_313
  30 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 187 (accept_3_3 29
  151 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 187
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 151 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 151 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 187 (accept_3_3 26 151 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 151 187 (Polychromatic418967fa.accept_13_12_8_5_1_976 25 151 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 187
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 187 (accept_3_3 23 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 187 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 187 (Polychromatic418967fa.accept_15_6_1_7_1_4079 21 151 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 187 (accept_3_3 20 151 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 187 (Polychromatic418967fa.accept_16_3_7_11_1_1723 19 151
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 187
  (Polychromatic418967fa.accept_16_2_7_11_1_1698 18 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 187 (accept_3_3 17 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 187 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 187 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 151 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 187 (accept_3_3 14 151 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 151 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 187
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 187 (accept_3_3 11 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 187 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 187 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 151 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 187 (accept_3_3 8 151 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 187 (Polychromatic418967fa.accept_21_7_4_19_1_4525 7 151 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 187
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 187 (accept_3_3 5 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 187 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 151 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 187 (Polychromatic418967fa.accept_13_3_8_5_1_974 3 151 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 187 (accept_3_3 2 151 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 187 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 151 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 187))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 150 187 (Eq.refl Bool.true) (allA_succ_of_accept 37 150 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 187
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 150 187 (accept_3_3 35 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 150 187 (Polychromatic418967fa.accept_16_2_6_11_1_1722 34 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 150 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 187 (accept_3_3 32 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 187 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 150 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 187
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 150 187 (accept_3_3 29 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 150 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 187 (Polychromatic418967fa.accept_18_9_6_7_1_6719 27 150 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 187 (accept_3_3 26 150 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 150 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 187
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 150 187 (accept_3_3 23 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 150 187 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 150 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 187 (accept_3_3 20 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 150 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 187
  (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 187 (accept_3_3 17 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 150 187 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 150 187 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 187 (accept_3_3 14 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 187
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 187 (accept_3_3 11 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 187 (accept_3_3 8 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 187 (Polychromatic418967fa.accept_19_7_17_16_1_6478 7 150 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 187
  (Polychromatic418967fa.accept_21_6_3_19_1_10785 6 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 187 (accept_3_3 5 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 187 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 150 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 187 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 187 (accept_3_3 2 150 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 187))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 149 187 (Eq.refl Bool.true) (allA_of_3_1 39 149 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 148 187 (Eq.refl Bool.true) (allA_succ_of_accept 39 148 187 (Polychromatic418967fa.accept_6_3_4_1_1_8
  39 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 187 (accept_3_3 38
  148 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 187
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 148 187 (Polychromatic418967fa.accept_15_6_13_7_1_222 36 148 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 148 187 (accept_3_3 35 148 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 148 187 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 148 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 187 (accept_3_3 32
  148 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 187
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 148 187 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 148 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 148 187 (accept_3_3 29 148 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 148 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 148 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 27
  148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 187 (accept_3_3 26
  148 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 187
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 148 187 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 148 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 148 187 (accept_3_3 23 148 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 148 187 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 148 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 148 187 (accept_3_3 20 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 148 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 148 187 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 148 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 187 (accept_3_3 17 148 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 187 (Polychromatic418967fa.accept_18_16_4_7_1_2927 16 148 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 148 187 (accept_3_3 14 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 148 187 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 148 187 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 148 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 187 (accept_3_3 11 148 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 187 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 148 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 148 187 (accept_3_3 8 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  148 187 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 148 187 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 148 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 187 (accept_3_3 5 148 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 187 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 148 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 148 187 (accept_3_3 2 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  148 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 148 187)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 147 187 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 147 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 187 (Polychromatic418967fa.accept_16_7_3_11_1_3682 39 147
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 187 (accept_3_3 38 147
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 187 (Polychromatic418967fa.accept_9_1_3_7_1_6
  37 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 187
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 147 187 (accept_3_3 35 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 147 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 147 187 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 147 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 187 (accept_3_3 32 147 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 187 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 147 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 187
  (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 187 (accept_3_3 29 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 147 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 147 187 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 147 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 187 (accept_3_3 26 147 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 187 (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 147
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 187
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 187 (accept_3_3 23 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 147 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 187 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 147 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 187 (accept_3_3 20 147 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 147 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 187
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 187 (accept_3_3 17 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 187 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 147 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 187 (accept_3_3 14 147 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 187 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 147 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 187
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 187 (accept_3_3 11 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 147 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 187 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 147 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 187 (accept_3_3 8 147 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 187 (Polychromatic418967fa.accept_16_7_3_11_1_3682 7 147 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 187
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 187 (accept_3_3 5 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 187 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 147 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 187 (accept_3_3 2 147 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 147 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  187))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 146 187 (Eq.refl Bool.true) (allA_of_3_1 42 146 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 145 187 (Eq.refl Bool.true) (allA_succ_of_accept 42 145 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 187 (accept_3_3 41 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 187 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 187 (accept_3_3 38 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 187 (Polychromatic418967fa.accept_23_14_7_3_1_10784 37 145 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 187
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 187 (accept_3_3 35 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 187 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 187 (accept_3_3 32 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 145 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 145 187 (accept_3_3 29 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 145 187 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 187 (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 145 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 187 (accept_3_3 26 145 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 187 (Polychromatic418967fa.accept_13_12_2_5_1_1634 25 145
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 187
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 187 (accept_3_3 23 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 187 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 187 (accept_3_3 20 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 187 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 145 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 187 (accept_3_3 17 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 187 (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 187 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 187 (accept_3_3 14 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 145 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 187
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 187 (accept_3_3 11 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 187 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 187 (accept_3_3 8 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 187 (Polychromatic418967fa.accept_13_7_2_5_1_2344 7 145 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 187
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 187 (accept_3_3 5 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 145 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 187 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 187 (accept_3_3 2 145 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 187 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 145 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 187)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 144 187 (Eq.refl Bool.true) (allA_succ_of_accept 43 144 187 (Polychromatic418967fa.accept_7_1_4_5_1_35
  43 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 144 187
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 144 187 (accept_3_3 41 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 144 187 (Polychromatic418967fa.accept_19_2_11_16_1_6525 40 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 144 187 (Polychromatic418967fa.accept_25_14_19_12_1_10783 39 144 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 187 (accept_3_3 38 144 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 187 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 144 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 144 187
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 144 187 (accept_3_3 35 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 144 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 144 187 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 144 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 187 (accept_3_3 32 144 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 187 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 144
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 187
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 144 187 (accept_3_3 29 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 144 187 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 144 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 144 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 187 (accept_3_3 26 144 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 187 (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 144 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 187
  (Polychromatic418967fa.accept_19_5_11_16_1_8010 24 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 144 187 (accept_3_3 23 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 144 187 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 144 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 187 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 144
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 187 (accept_3_3 20 144
  187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 187
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 144 187 (Polychromatic418967fa.accept_22_18_12_11_1_5892 18 144 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 187 (accept_3_3 17 144 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 187 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 144 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 187
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 144 187 (accept_3_3 14 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 144 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 144 187 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 144 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 187 (accept_3_3 11 144 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 187 (Polychromatic418967fa.accept_22_10_12_11_1_7412 10
  144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 187
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 187 (accept_3_3 8 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  144 187 (Polychromatic418967fa.accept_21_7_18_19_1_10715 7 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 187 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 144 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 187 (accept_3_3 5 144 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 187 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 144 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 187
  (Polychromatic418967fa.accept_10_3_4_7_1_353 3 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 187 (accept_3_3 2 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 187 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 144 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 187)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 143 187 (Eq.refl Bool.true)
  (allA_of_3_1 45 143 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 142 187 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 142 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 187 (accept_3_3 44 142 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 142 187 (Polychromatic418967fa.accept_13_4_12_5_1_476 43 142 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 187
  (Polychromatic418967fa.accept_19_4_9_16_1_3811 42 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 187 (accept_3_3 41 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 187 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 187 (accept_3_3 38 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 187
  (Polychromatic418967fa.accept_22_14_10_11_1_7472 36 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 142 187 (accept_3_3 35 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 142 187 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 142 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 187 (accept_3_3 32 142 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 187 (Polychromatic418967fa.accept_7_3_2_5_1_147
  31 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 187
  (Polychromatic418967fa.accept_13_4_12_5_1_476 30 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 187 (accept_3_3 29 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 187 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 187 (accept_3_3 26 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 187
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 187 (accept_3_3 23 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 187 (Polychromatic418967fa.accept_18_4_16_7_1_1873 22 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 187 (accept_3_3 20 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 187 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 142 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 187
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 187 (accept_3_3 17 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 187 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 187 (accept_3_3 14 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 187
  (Polychromatic418967fa.accept_19_12_9_16_1_5086 12 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 142 187 (accept_3_3 11 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 142 187 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 142 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 187 (accept_3_3 8 142 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 187 (Polychromatic418967fa.accept_13_7_12_5_1_1603
  7 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 187
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 187 (accept_3_3 5 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 187 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 142 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 187 (accept_3_3 2 142 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 187))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 141 187 (Eq.refl Bool.true) (allA_succ_of_accept 46 141 187 (Polychromatic418967fa.accept_4_2_1_3_1_27
  46 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 187
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 187 (accept_3_3 44 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 141 187 (Polychromatic418967fa.accept_15_13_6_7_1_1369 43 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 187 (accept_3_3 41 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 187
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 187 (accept_3_3 38 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 187 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 141 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 187 (accept_3_3 35 141 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 187
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 187 (accept_3_3 32 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 187 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 187 (accept_3_3 29 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 187
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 187 (accept_3_3 26 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 187 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 187 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 187 (accept_3_3 23 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 187
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 187 (accept_3_3 20 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 187 (accept_3_3 17 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 187
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 187 (accept_3_3 14 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 187 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 187 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 187 (accept_3_3 11 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 187
  (Polychromatic418967fa.accept_19_9_8_16_1_5101 9 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 187 (accept_3_3 8 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 187 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 187 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 187 (accept_3_3 5 141 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 187 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 187
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 187 (accept_3_3 2 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 187 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 141 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 187))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 140 187 (Eq.refl
  Bool.true) (allA_of_3_1 48 140 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 139 187 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 139 187 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 139 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 187 (accept_3_3 47 139 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 139 187 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 187
  (Polychromatic418967fa.accept_19_7_6_16_1_3818 45 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 187 (accept_3_3 44 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 187 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 187 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 187 (accept_3_3 41 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 187 (Polychromatic418967fa.accept_13_1_9_5_1_1598 40 139 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 187
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 187 (accept_3_3 38 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 187 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 187 (accept_3_3 35 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 187 (Polychromatic418967fa.accept_14_6_13_5_1_534 34 139 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 187
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 187 (accept_3_3 32 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 187 (Polychromatic418967fa.accept_19_12_6_16_1_10731 31 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 187 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 139 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 187 (accept_3_3 29 139 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 139 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 187
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 187 (accept_3_3 26 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 187 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 187 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 187 (accept_3_3 23 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 187 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 139 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 187
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 187 (accept_3_3 20 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 187 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 187 (accept_3_3 17 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 187 (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 139 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 187
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 187 (accept_3_3 14 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 187 (Polychromatic418967fa.accept_23_13_1_3_1_10782 13 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 187 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 187 (accept_3_3 11 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 187 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 139 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 187
  (Polychromatic418967fa.accept_19_9_6_16_1_5116 9 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 187 (accept_3_3 8 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 187 (Polychromatic418967fa.accept_19_7_6_16_1_3818 7 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 187 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 187 (accept_3_3 5 139 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 187 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 139 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 187
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 187 (accept_3_3 2 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 187 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 139 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 187))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 138 187 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 138 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 187
  (Polychromatic418967fa.accept_19_10_5_16_1_6522 48 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 187 (accept_3_3 47 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 138 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 138 187 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 187 (accept_3_3 44 138 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 187
  (Polychromatic418967fa.accept_21_1_12_19_1_7721 43 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 138 187 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 138 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 138 187 (accept_3_3 41 138 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 187 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 187
  (Polychromatic418967fa.accept_10_9_8_7_1_714 39 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 138 187 (accept_3_3 38 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 138 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 138 187 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 138 187 (accept_3_3 35 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 187 (Polychromatic418967fa.accept_15_4_3_7_1_713 34 138
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 187
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 138 187 (accept_3_3 32 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 138 187 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 138 187 (Polychromatic418967fa.accept_19_11_5_16_1_1456 30 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 187 (accept_3_3 29 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 138 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 187
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 138 187 (accept_3_3 26 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 138 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 138 187 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 138 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 187 (accept_3_3 23 138 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 187 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 187
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 138 187 (accept_3_3 20 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 138 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 138 187 (Polychromatic418967fa.accept_21_18_12_19_1_10725 18 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 187 (accept_3_3 17 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 187 (Polychromatic418967fa.accept_13_3_8_5_1_974 16 138
  187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 187
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 138 187 (accept_3_3 14 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 138 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 138 187 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 187 (accept_3_3 11 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 187 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 138 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 187
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 138 187 (accept_3_3 8 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  138 187 (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 138 187 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 138 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 187 (accept_3_3 5 138 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 187 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 138 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 187
  (Polychromatic418967fa.accept_13_3_8_5_1_974 3 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 138 187 (accept_3_3 2 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  138 187 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 138 187)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 137 187 (Eq.refl
  Bool.true) (allA_of_3_1 51 137 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 136 187 (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 136 187 17 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 136 187 (accept_3_3 50 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 136 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 136 187 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 136 187 (accept_3_3 47 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 136 187 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 136 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 136 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 136 187 (accept_3_3 44 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 136 187 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 136 187 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 136 187 (accept_3_3 41 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 136 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 136 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 136 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 136 187 (accept_3_3 38 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 136 187 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 136 187 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 136 187 (accept_3_3 35 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 187 17 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 187 (accept_3_3 32 136 187
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 187 (Polychromatic418967fa.accept_9_4_1_7_1_293
  31 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 187
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 187 (accept_3_3 29 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 187 (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 187 (accept_3_3 26 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 187 (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 136 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 187
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 187 (accept_3_3 23 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 187 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 187 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 187 (accept_3_3 20 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 187 (Polychromatic418967fa.accept_16_3_8_11_1_2714 19 136 187
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 187
  (Polychromatic418967fa.accept_19_18_3_16_1_7962 18 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 17 136 187 17 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 16 136 187 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 136 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 136 187 (accept_3_3 14 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 136 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 136 187 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 187 (accept_3_3 11 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 187 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 136 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 187 (accept_3_3 8 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 187 (Polychromatic418967fa.accept_21_7_10_19_1_10739 7 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 187 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 187 (accept_3_3 5 136 187 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 187 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 136 187 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 187
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 187 (accept_3_3 2 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 187 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 136 187 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136 187))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_187_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))


