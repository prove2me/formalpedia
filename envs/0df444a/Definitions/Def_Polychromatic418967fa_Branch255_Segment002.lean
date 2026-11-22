-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch255_Segment002
-- name    : Polychromatic418967fa_Branch255_Segment002
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:47:04.031169+00:00
-- url     : https://prove2.me/theorems/2ea88b83-ec62-4a6f-afec-6481ec19caf9
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch255_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_255_segment_002 : allB 198 255 :=
  allB_succ' 59 197 255 (Eq.refl Bool.true) (allA_succ_of_accept 58 197 255 (accept_3_4 58 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 197 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 197 255 (accept_3_4 55 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 197 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 197 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 255 (accept_3_4 52 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 197 255 (accept_3_4 49 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 197 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 197 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 255 (accept_3_4 46 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 255 (accept_3_4 43 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 255 (accept_3_4 40 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 255 (accept_3_4 37 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 255 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 255 (Polychromatic418967fa.accept_19_16_7_8_1_8820 35 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 255 (accept_3_4 34 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 197 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 255 (accept_3_4 31 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 255 (accept_3_4 28 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 255 (Polychromatic418967fa.accept_21_6_8_3_1_11140 27 197 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 255 (accept_3_4 25 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 255 (accept_3_4 22 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 255 (accept_3_4 19 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 255 (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 255 (accept_3_4 16 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 197 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 255 (accept_3_4 13 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 255 (accept_3_4 10 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 255 (accept_3_4 7 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 255 (accept_3_4 4 197 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 197 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 255 (accept_3_4 1 197 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 196 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 196 255 (accept_3_5 59 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 196 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 196 255 (Polychromatic418967fa.accept_13_5_1_8_1_1115 57 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 196 255 (accept_3_5 56 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 196 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 196 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 196 255 (accept_3_5 53 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 196 255 (Polychromatic418967fa.accept_19_14_6_8_1_15595 52 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 196 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 196 255 (accept_3_5 50 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 196 255
  (Polychromatic418967fa.accept_11_4_9_2_1_259 48 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 196 255 (accept_3_5 47 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 196 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 196 255 (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 196 255 (accept_3_5 44 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 196 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 196 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 196 255 (accept_3_5 41 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 196 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 196 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 196 255 (accept_3_5 38 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 196 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 196 255
  (Polychromatic418967fa.accept_19_17_6_8_1_5928 36 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 196 255 (accept_3_5 35 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 196 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 196 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 196 255 (accept_3_5 32 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 196 255
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 196 255 (accept_3_5 29 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 196 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 196 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 196 255 (accept_3_5 26 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 196 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 196 255 (accept_3_5 23 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 196 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 196 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 196 255 (accept_3_5 20 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 196 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 196 255
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 196 255 (accept_3_5 17 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 196 255 (Polychromatic418967fa.accept_19_16_6_8_1_8772 16 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 196 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 196 255 (accept_3_5 14 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 196 255
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 196 255 (accept_3_5 11 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 196 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 196 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 255 (accept_3_5 8 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 196 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 196 255 (accept_3_5 5 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  196 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 196 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 196 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 255 (accept_3_5 2 196 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 196 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 195 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 195 255 15 4 13 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 195 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 195 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 255 (Polychromatic418967fa.accept_7_2_6_3_1_100
  58 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 195 255 3 19 65 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 195 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 195 255 5 11 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 195 255 3 18 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 195 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 195 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 52 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 195 255 3 17 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 195 255 5 10 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 195 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 195 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 195 255 3 16 65 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 195 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 195 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 195 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 195 255 15 3 13 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 195 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 44
  195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 195 255 3 14 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 195 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 195 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 195 255 5 8 39 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 195 255 3 13 65 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 195 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 195 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 195 255 3 12 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 195 255 5 7 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 195 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 34
  195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 195 255 3 11 65 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 195 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 195 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 195 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 255 15 2 13 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 195 255 3 9 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 195 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 195 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 195 255 5 5 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 195 255 3 8 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 195 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 195 255 3 7 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 195 255 5 4 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 195 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 195 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 255 3 6 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 195 255 15 1 13 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 195 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 195 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  13 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 195 255 3 4 65 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 195 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 195 255 5 2 39 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 195 255 3 3 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 195 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 195 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 195 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 255 3 2 65 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 195 255 5 1 39 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 195 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 195 255 3 1 65 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 195 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 195 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 195 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 194 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 194 255 (accept_3_4 61 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 194 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 194 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 194 255 (accept_3_4 58 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 194 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 194 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 194 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 194 255 (accept_3_4 55 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 194 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 194 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 194 255 (accept_3_4 52 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 194 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 194 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 194 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 194 255 (accept_3_4 49 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 194 255 (Polychromatic418967fa.accept_13_9_12_8_1_570 48 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 194 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 194 255 (accept_3_4 46 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 194 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 194 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 194 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 194 255 (accept_3_4 43 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 194 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 194 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 194 255 (accept_3_4 40 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 194 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 194 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 194 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 194 255 (accept_3_4 37 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 194 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 194 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 255 (accept_3_4 34 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 194 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 255
  (Polychromatic418967fa.accept_19_13_4_8_1_11571 32 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 194 255 (accept_3_4 31 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 194 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 194 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 194 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 194 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 255 (accept_3_4 28 194 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 255
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 194 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 194 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 194 255 (accept_3_4 25 194 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 194 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 194 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 255 (accept_3_4 22
  194 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 194 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 194 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 194 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 194 255 (accept_3_4 19 194 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 194 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 194 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 194 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 194 255 (accept_3_4 16 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 194 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 194 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 194 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 194 255 (accept_3_4 13 194 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 194 255 (Polychromatic418967fa.accept_16_12_2_15_1_490 12 194
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 194 255 (accept_3_4 10 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  194 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 194 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 194 255 (accept_3_4 7 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 194 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 194 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 194 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 194 255 (accept_3_4 4 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  194 255 (Polychromatic418967fa.accept_16_3_2_15_1_7367 3 194 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 194 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 194 255 (accept_3_4 1 194 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 194 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  193 255 (Eq.refl Bool.true) (allA_succ_of_accept 62 193 255 (accept_3_5 62 193 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 193 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 193 255 (Polychromatic418967fa.accept_9_6_4_3_1_203
  60 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 193 255 (accept_3_5 59
  193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 193 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 193 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 193 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 255 (accept_3_5 56 193 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 193 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 193 255 (accept_3_5 53
  193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 193 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 52 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 193 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 193 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 255 (accept_3_5 50 193 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 193 255 (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 255 (accept_3_5 47 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 255 (accept_3_5 44 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 193 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 255 (accept_3_5 41 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 255 (Polychromatic418967fa.accept_21_18_4_3_1_8082 39 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 255 (accept_3_5 38 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 193 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 255 (accept_3_5 35 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 255 (accept_3_5 32 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 255 (Polychromatic418967fa.accept_20_11_13_15_1_6931 31 193 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 255 (accept_3_5 29 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 255 (accept_3_5 26 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 255 (accept_3_5 23 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 255 (accept_3_5 20 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 193 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 255 (accept_3_5 17 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 255 (accept_3_5 14 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 255
  (Polychromatic418967fa.accept_10_2_3_5_1_996 12 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 255 (accept_3_5 11 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 255 (accept_3_5 8 193 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 255 (accept_3_5 5 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 193 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 255 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 255 (accept_3_5 2 193 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 193 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 192 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 192 255 3 21 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 192 255 (Polychromatic418967fa.accept_14_6_10_3_1_1038 62 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 192 255
  (Polychromatic418967fa.accept_18_7_12_3_1_804 61 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 192 255 3 20 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 192 255 (Polychromatic418967fa.accept_13_7_10_8_1_567 59 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 192 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 58 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 192 255 3 19 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 192 255 (Polychromatic418967fa.accept_13_4_10_8_1_1817 56 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 192 255
  (Polychromatic418967fa.accept_14_13_10_3_1_1037 55 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 192 255 3 18 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 192 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 192 255
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 192 255 3 17 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 192 255 (Polychromatic418967fa.accept_13_11_10_8_1_1804 50 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 192 255
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 49 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 255 3 16 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 192 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 47 192 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 192 255 (Polychromatic418967fa.accept_13_7_10_8_1_567
  46 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 192 255 3 15 64 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 192 255
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 44 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 192 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 192 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 192 255 3 14 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 192 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629
  41 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 255
  (Polychromatic418967fa.accept_22_18_16_13_1_10902 40 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 192 255 3 13 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 192 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 192 255
  (Polychromatic418967fa.accept_10_7_2_5_1_298 37 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 255 3 12 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 255 (Polychromatic418967fa.accept_14_7_10_3_1_1034 35 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 255
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 192 255 3 11 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 192 255 (Polychromatic418967fa.accept_18_14_12_3_1_5103 32 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 192 255
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 31 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 255 3 10 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 192 255 (Polychromatic418967fa.accept_19_10_2_8_1_3206 29 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 192 255 3 9 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 192 255 (Polychromatic418967fa.accept_18_8_12_3_1_2708 26 192 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 255 (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 192
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 255 3 8 64 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 255
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 192 255 (Polychromatic418967fa.accept_25_22_17_5_1_15606 22 192 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 192 255 3 7 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 192 255
  (Polychromatic418967fa.accept_13_7_10_8_1_567 20 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 192 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 192 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 255 3 6 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 255 (Polychromatic418967fa.accept_10_7_2_5_1_298
  17 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 255
  (Polychromatic418967fa.accept_23_16_8_2_1_9042 16 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 192 255 3 5 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 192 255 (Polychromatic418967fa.accept_18_14_12_3_1_5103 14 192 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 255 (Polychromatic418967fa.accept_10_3_2_5_1_295
  13 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 255 3 4 64 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 255
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 192 255 (Polychromatic418967fa.accept_19_10_2_8_1_3206 10 192 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 192 255 3 3 64 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 192 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 192 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 192 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 255 3 2 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 255 (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 192 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 255
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 192 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 192 255 3 1 64 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 192 255 (Polychromatic418967fa.accept_13_2_10_8_1_1126 2 192 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 255 (Polychromatic418967fa.accept_18_1_12_3_1_6426 1 192
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 191 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 191 255 (accept_3_4 64 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 191 255 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 191 255 (accept_3_4 61 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 191 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 191 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 191 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 191 255 (accept_3_4 58 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 191 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 191 255 (accept_3_4 55 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 191 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 191 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 191 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 191 255 (accept_3_4 52 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 191 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 191 255 (accept_3_4 49 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 191 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 191 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 191 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 191 255 (accept_3_4 46 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 191 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 191 255 (accept_3_4 43 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 191 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 191 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 191 255 (accept_3_4 40 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 191 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 255 (accept_3_4 37 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 191 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 255 (accept_3_4 34 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 255 (accept_3_4 31 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 255 (Polychromatic418967fa.accept_13_4_9_8_1_1736 30 191 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 255 (accept_3_4 28 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 255 (accept_3_4 25 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 191 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 255 (accept_3_4 22 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 255 (accept_3_4 19 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 255 (Polychromatic418967fa.accept_19_18_1_8_1_7291 18 191 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 255 (accept_3_4 16 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 255 (accept_3_4 13 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 191 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 255
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 255 (accept_3_4 10 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 255 (accept_3_4 7 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 191 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 255 (accept_3_4 4 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 255 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 191 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 255 (accept_3_4 1 191 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66
  190 255 (Eq.refl Bool.true) (allA_succ_of_gcd 65 190 255 5 13 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 190 255 (Polychromatic418967fa.accept_20_4_10_15_1_6919 64 190
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 190 255
  (Polychromatic418967fa.accept_20_3_10_15_1_620 63 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 190 255 (accept_3_5 62 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 190 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 190 255 5 12 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 190 255 (accept_3_5 59 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 190 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 190 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 190 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 190 255 (accept_3_5 56 190 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 190 255 5 11 38 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 190 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 190 255 (accept_3_5 53 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 190 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 190 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 190 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 190 255 5 10 38 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 190 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 190 255 (Polychromatic418967fa.accept_20_8_10_15_1_6922 48 190 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 190 255 (accept_3_5 47 190 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 190 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 190 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 190 255 5 9 38 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 190 255 (accept_3_5 44 190 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 190 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43
  190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 190 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 190 255 (accept_3_5 41 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  190 255 5 8 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 190 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 190 255 (accept_3_5 38 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 190 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 190 255 (Polychromatic418967fa.accept_16_4_14_15_1_6331 36 190
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 190 255 5 7 38 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 190 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 190 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 190 255 (accept_3_5 32 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 190 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 190 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 190 255 5 6 38 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 190 255 (accept_3_5 29 190 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 190 255 (Polychromatic418967fa.accept_20_8_10_15_1_6922 28 190
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 190 255
  (Polychromatic418967fa.accept_20_7_10_15_1_14095 27 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 190 255 (accept_3_5 26 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 190 255 5 5 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 190 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 190 255 (accept_3_5 23 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 190 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 190 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 190 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 255 5 4 38 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 190 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 190 255 (accept_3_5 17 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 190 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 190 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 190 255 5 3 38 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 190 255 (accept_3_5 14 190 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 190 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 190 255 (accept_3_5 11 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  190 255 5 2 38 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 190 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 190 255 (accept_3_5 8 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 190 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 190 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 190 255 5 1 38 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 190 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 190 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 190 255 (Polychromatic418967fa.accept_20_3_10_15_1_620 3 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 255 (accept_3_5 2 190 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 190 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 189 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 189 255 3 22 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 189 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 189 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 255 (Polychromatic418967fa.accept_10_4_9_5_1_84
  64 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 189 255 3 21 63 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 189 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 189 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 61 189 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 189 255 3 20 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 189 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  59 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 189 255 3 19 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 189 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 189 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 189 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 189 255 3 18 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 189 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 189 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 255
  (Polychromatic418967fa.accept_14_10_7_3_1_1022 52 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 189 255 3 17 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 189 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 189 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 255 (Polychromatic418967fa.accept_12_1_9_3_1_370
  49 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 189 255 3 16 63 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 189 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 47 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 189 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 189 255 3 15 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 189 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 44
  189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 189 255 3 14 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 189 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 189 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 255 (Polychromatic418967fa.accept_13_1_7_8_1_1796
  40 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 189 255 3 13 63 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 189 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 189 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 189 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 189 255 3 12 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 189 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  35 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 189 255 3 11 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 189 255 (Polychromatic418967fa.accept_14_4_7_3_1_1718 32 189 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 31 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 189 255 3 10 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 189 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 189 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 255 (Polychromatic418967fa.accept_13_2_7_8_1_4221
  28 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 189 255 3 9 63 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 189 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 189 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 189 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 189 255 3 8 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 189 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  23 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 189 255 3 7 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 189 255 (Polychromatic418967fa.accept_18_2_9_3_1_3825 20 189 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 189
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 189 255 3 6 63 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 189 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 189 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 189 255 3 5 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 189 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 189 255 3 4 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 189 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 189 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 189 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 255 3 3 63 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 255
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 8 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 189 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 255 3 2 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 189 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 255
  (Polychromatic418967fa.accept_10_4_9_5_1_84 4 189 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 189 255 3 1 63 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 189 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 189 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 188 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 188 255 (accept_3_4 67 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 188 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 188 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 188 255 (accept_3_4 64 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 188 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 188 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 188 255
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 188 255 (accept_3_4 61 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 188 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 188 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 188 255 (accept_3_4 58 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 188 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 188 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 188 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 188 255 (accept_3_4 55 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 188 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 188 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 188 255 (accept_3_4 52 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 188 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 188 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 188 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 188 255 (accept_3_4 49 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 188 255 (Polychromatic418967fa.accept_18_12_8_3_1_1627 48 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 188 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 188 255 (accept_3_4 46 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 188 255 (Polychromatic418967fa.accept_16_13_12_15_1_6290 45 188 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 188 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 188 255 (accept_3_4 43 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 188 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 188 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 188 255 (accept_3_4 40 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 188 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 188 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 188 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 188 255 (accept_3_4 37 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 188 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 188 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 188 255 (accept_3_4 34 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 188 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 188 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 188 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 188 255 (accept_3_4 31 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 188 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 188 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 188 255 (accept_3_4 28 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 188 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 188 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 188 255
  (Polychromatic418967fa.accept_22_4_12_13_1_10855 26 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 188 255 (accept_3_4 25 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 188 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 188 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 188 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 188 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 188 255 (accept_3_4 22 188 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 188 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 188 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 188 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 188 255 (accept_3_4 19 188 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 188 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 188 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 188 255 (accept_3_4 16
  188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 188 255
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 188 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 188 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 255 (accept_3_4 13 188 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 188 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 188 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 188 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 188 255 (accept_3_4 10 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  188 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 188 255 (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 188 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 255 (accept_3_4 7 188 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 188 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 188 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 188 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 188 255 (accept_3_4 4 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  188 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 188 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 188 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 255 (accept_3_4 1 188 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  69 187 255 (Eq.refl Bool.true) (allA_succ_of_gcd 68 187 255 17 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 187 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 67
  187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 187 255
  (Polychromatic418967fa.accept_13_1_5_8_1_207 66 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 187 255 (accept_3_5 65 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 187 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 187 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 187 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 187 255 (accept_3_5 62 187 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 187 255 (Polychromatic418967fa.accept_20_1_7_15_1_1521 61 187
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 187 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 187 255 (accept_3_5 59 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 187 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 187 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 187 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 187 255 (accept_3_5 56 187 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 187 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 187 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 187 255
  (Polychromatic418967fa.accept_14_12_5_3_1_1011 54 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 187 255 (accept_3_5 53 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 187 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 187 255 17 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 187 255 (accept_3_5 50 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 187 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 187 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 187
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 187 255 (accept_3_5 47 187
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 187 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 46 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 187 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 255 (accept_3_5 44 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 187 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 187 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 187 255 (Polychromatic418967fa.accept_9_6_7_3_1_436
  42 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 255 (accept_3_5 41
  187 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 187 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 40 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 187 255 (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 187 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 255 (accept_3_5 38 187 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 187 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 187 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 187 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 187 255 (accept_3_5 35 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  187 255 17 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 187 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 255 (accept_3_5 32 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 187 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 187 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30
  187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 255 (accept_3_5 29
  187 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 187 255 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 255 (accept_3_5 26 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 187 255 (Polychromatic418967fa.accept_13_12_5_8_1_1101 25 187 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 255 (accept_3_5 23 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 187 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 255 (accept_3_5 20 187 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 187 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 255
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 17 187 255 17 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 16 187 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 187 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 255 (Polychromatic418967fa.accept_7_1_5_3_1_268
  15 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 255 (accept_3_5 14
  187 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 255
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 187 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 255 (accept_3_5 11 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 187 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 187 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9
  187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 255 (accept_3_5 8 187
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 255
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 7 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 187 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 255 (accept_3_5 5 187 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 187 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 187 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3
  187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 255 (accept_3_5 2 187
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 187 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 187 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 186 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 186 255 3 23 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 186 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 186 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 186 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 255 3 22 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 186 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 186 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 64
  186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 186 255 3 21 62 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 186 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 186 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 186 255 3 20 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 186 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 186 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 186 255 3 19 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 186 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 186 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 186 255 (Polychromatic418967fa.accept_7_6_4_3_1_266
  55 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 186 255 3 18 62 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 186 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 186 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 186 255 3 17 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 186 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 50
  186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 186 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 255 3 16 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 186 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 186 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 186 255 3 15 62 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 186 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 186 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 186 255 3 14 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 186 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 186 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 186 255 3 13 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 186 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 186 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 186 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 186 255 3 12 62 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 186 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 186 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 186 255 3 11 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 186 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 186 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 255 3 10 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 186 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 186 255 3 9 62 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 186 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 186 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 186 255 3 8 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 186 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 186 255 3 7 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 186 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 186 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 186 255 3 6 62 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 186 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 186 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 186 255 3 5 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 186 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 255 3 4 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 186 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 186 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 186 255 3 3 62 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 186 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 255 3 2 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 186 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 186 255 3 1 62 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 186 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 186 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 185 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 185 255 5 14 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 185 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 185 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68
  185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 185 255 (accept_3_4 67
  185 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 185 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 185 255 5 13 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 185 255 (accept_3_4 64 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 185 255 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 185 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 185 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 185 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 185 255 (accept_3_4 61 185 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 185 255 5 12 37 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 185 255
  (Polychromatic418967fa.accept_11_4_9_2_1_259 59 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 185 255 (accept_3_4 58 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 185 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 185 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 185 255 5 11 37 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 185 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 185 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 185 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 185 255 (accept_3_4 52 185 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 185 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 185 255 5 10 37 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 185 255 (accept_3_4 49 185 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 185 255 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 185
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 185 255 (accept_3_4 46 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  185 255 5 9 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 185 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 185 255 (accept_3_4 43 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 185 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 185 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 255 (Polychromatic418967fa.accept_19_3_14_8_1_3272 41 185
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 185 255 5 8 37 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 185 255
  (Polychromatic418967fa.accept_20_19_5_15_1_5380 39 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 185 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 255 (accept_3_4 37 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 185 255 (Polychromatic418967fa.accept_20_16_5_15_1_5364 36 185 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 185 255 5 7 37 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 185 255 (accept_3_4 34
  185 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 185 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 185 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 255 (accept_3_4 31 185 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 185 255 5 6 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 185 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 185 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 255 (accept_3_4 28 185 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 255 (Polychromatic418967fa.accept_20_7_5_15_1_1548 27 185
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 185 255 5 5 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 185 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 185 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 255 (Polychromatic418967fa.accept_19_4_14_8_1_4510 23 185
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 255 (accept_3_4 22 185
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 255
  (Polychromatic418967fa.accept_12_9_5_3_1_782 21 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 185 255 5 4 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 185 255 (accept_3_4 19 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 255 (accept_3_4 16 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 185 255 5 3 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 185 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 185 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 255 (accept_3_4 13 185 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 255
  (Polychromatic418967fa.accept_20_12_5_15_1_14100 12 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 185 255 5 2 37 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 185 255
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 185 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 185 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 255 (accept_3_4 7 185 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 185 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 185 255 5 1 37 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 185 255 (accept_3_4 4 185 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 255 (Polychromatic418967fa.accept_19_3_14_8_1_3272 3 185 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 255 (accept_3_4 1 185 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 184 255 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 184 255 (accept_3_5 71 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 184 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 184 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 184 255 (accept_3_5 68 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 184 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 66 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 184 255 (accept_3_5 65 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 184 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 184 255 (Polychromatic418967fa.accept_19_6_13_8_1_4508 63 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 184 255 (accept_3_5 62 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 184 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 184 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 184 255 (accept_3_5 59 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 184 255 (Polychromatic418967fa.accept_13_6_2_8_1_1782 58 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 184 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 184 255 (accept_3_5 56 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 184 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 184 255 (accept_3_5 53 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 184 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 184 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 184 255 (accept_3_5 50 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 184 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 184 255 (accept_3_5 47 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 184 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 184 255 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 184 255 (accept_3_5 44 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 184 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 184 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 184 255 (accept_3_5 41 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 184 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 184 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 184 255 (accept_3_5 38 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 184 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 184 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 184 255 (accept_3_5 35 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 184 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 184 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 184 255 (accept_3_5 32 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 184 255
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 184 255 (accept_3_5 29 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 184 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 184 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 184 255 (accept_3_5 26 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 184 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 184 255 (accept_3_5 23 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 184 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 184 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 184 255 (accept_3_5 20 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 184 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 184 255
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 184 255 (accept_3_5 17 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 184 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 184 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 184 255 (accept_3_5 14 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 184 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 184 255 (accept_3_5 11 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 184 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 184 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 255 (accept_3_5 8 184 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 255 (accept_3_5 5 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 255 (Polychromatic418967fa.accept_16_4_8_15_1_1113 4 184 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 255 (Polychromatic418967fa.accept_19_3_13_8_1_4476 3 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 255 (accept_3_5 2 184 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 184 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 183 255 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 183 255 3 24 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 183 255 (Polychromatic418967fa.accept_13_6_1_8_1_1116 71 183 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 255
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 70 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 183 255 3 23 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 183 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 183 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 183 255 (Polychromatic418967fa.accept_7_4_1_3_1_277
  67 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 183 255 3 22 61 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 183 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 183 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 183 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 183 255 3 21 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 183 255 (Polychromatic418967fa.accept_10_2_3_5_1_996
  62 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 183 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 183 255 3 20 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 183 255 (Polychromatic418967fa.accept_13_7_1_8_1_1778 59 183 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 58 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 183 255 3 19 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 183 255 (Polychromatic418967fa.accept_16_8_7_15_1_6339 56 183 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 255
  (Polychromatic418967fa.accept_27_1_21_12_1_15605 55 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 183 255 3 18 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 183 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 183 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 255
  (Polychromatic418967fa.accept_10_2_3_5_1_996 52 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 183 255 3 17 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 183 255 (Polychromatic418967fa.accept_13_11_1_8_1_1776 50 183 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 255
  (Polychromatic418967fa.accept_19_11_12_8_1_11492 49 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 183 255 3 16 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 183 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 183 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 46 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 183 255 3 15 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 183 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 183 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 255
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 43 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 183 255 3 14 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 183 255 (Polychromatic418967fa.accept_22_19_7_13_1_6004 41 183 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 40 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 183 255 3 13 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 183 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 38 183 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 255 (Polychromatic418967fa.accept_7_2_1_3_1_102
  37 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 183 255 3 12 61 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 183 255
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 183 255 (Polychromatic418967fa.accept_19_15_12_8_1_5922 34 183 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 183 255 3 11 61 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 183 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 183 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 183 255 3 10 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 183 255
  (Polychromatic418967fa.accept_19_10_12_8_1_10124 29 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 183 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 183 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 183 255 3 9 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 183 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 183 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 183 255 3 8 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 183 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 23
  183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 255
  (Polychromatic418967fa.accept_10_2_3_5_1_996 22 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 183 255 3 7 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 183 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 183 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 183 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 183 255 3 6 61 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 183 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 183 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 183 255 3 5 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 255
  (Polychromatic418967fa.accept_16_14_7_15_1_3947 14 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 183 255 (Polychromatic418967fa.accept_25_13_8_5_1_15604 13 183 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 255 3 4 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 255 (Polychromatic418967fa.accept_19_10_12_8_1_10124 10 183 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 255 3 3 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 8
  183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 183 255 3 2 61 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 183 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 183 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 183 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 255 3 1 61 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 183 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 255 (Polychromatic418967fa.accept_19_1_12_8_1_8799 1 183 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 182 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 182 255 (accept_3_4 73 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 182 255 (Polychromatic418967fa.accept_21_9_14_3_1_9678 72 182 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 182 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 182 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 182 255 (accept_3_4 70 182 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 182 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 68 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 182 255 (accept_3_4 67 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 182 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 182 255 (accept_3_4 64 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 182 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 182 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 62 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 182 255 (accept_3_4 61 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 182 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 182 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 182 255 (accept_3_4 58 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 182 255
  (Polychromatic418967fa.accept_19_18_11_8_1_10080 56 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 182 255 (accept_3_4 55 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 182 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 182 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 182 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 182 255 (accept_3_4 52 182 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 182 255 (Polychromatic418967fa.accept_9_6_2_3_1_771
  51 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 182 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 182 255 (accept_3_4 49 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 182 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 182 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 182 255 (accept_3_4 46 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 182 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 182 255 (accept_3_4 43 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 182 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 182 255 (accept_3_4 40 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 182 255 (Polychromatic418967fa.accept_16_7_6_15_1_495 39 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 182 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 182 255 (accept_3_4 37 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 182 255 (Polychromatic418967fa.accept_19_17_11_8_1_11490 36 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 182 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 182 255 (accept_3_4 34 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 182 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 182 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 182 255 (accept_3_4 31 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 182 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 182 255 (accept_3_4 28 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 182 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 182 255 (accept_3_4 25 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 182 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 182 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 255 (accept_3_4 22 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 182 255
  (Polychromatic418967fa.accept_19_1_11_8_1_4504 20 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 182 255 (accept_3_4 19 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 182 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 255 (accept_3_4 16 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 182 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 182 255 (accept_3_4 13 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 182 255 (Polychromatic418967fa.accept_18_12_2_3_1_6414 12 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 182 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 255 (accept_3_4 10 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 182 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 182 255 (accept_3_4 7 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  182 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 182 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 255 (accept_3_4 4 182 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 182 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 255
  (Polychromatic418967fa.accept_19_2_11_8_1_2090 2 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 255 (accept_3_4 1 182 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 181 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 74 181 255 (accept_3_5 74 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 181 255 (Polychromatic418967fa.accept_19_16_10_8_1_10067 73 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 181 255 (Polychromatic418967fa.accept_7_2_6_3_1_100
  72 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 181 255 (accept_3_5 71
  181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 181 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 181 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 181 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 181 255 (accept_3_5 68 181 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 181 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 181 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 181 255 (accept_3_5 65
  181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 181 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 181 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 181 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 181 255 (accept_3_5 62 181 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 181 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 181 255 (Polychromatic418967fa.accept_7_4_6_3_1_271
  60 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 181 255 (accept_3_5 59
  181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 181 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 181 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 181 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 181 255 (accept_3_5 56 181 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 181 255 (Polychromatic418967fa.accept_19_17_10_8_1_5942 55 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 181 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 181 255 (accept_3_5 53 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 181 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 181 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 181 255 (accept_3_5 50 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 181 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 181 255
  (Polychromatic418967fa.accept_13_9_12_8_1_570 48 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 181 255 (accept_3_5 47 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 181 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 181 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 181 255 (accept_3_5 44 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 181 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 181 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 181 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 181 255 (accept_3_5 41 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 181 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 181 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 255 (accept_3_5 38 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 181 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 181 255
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 181 255 (accept_3_5 35 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 181 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 181 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 255 (accept_3_5 32 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 181 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 181 255 (accept_3_5 29 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 181 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 181 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 181 255 (accept_3_5 26 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 181 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 181 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 181 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 181 255 (accept_3_5 23 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 181 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 181 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 255 (accept_3_5 20 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 181
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 181 255 (accept_3_5 17 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 181 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 181 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 255 (accept_3_5 14 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 255
  (Polychromatic418967fa.accept_18_12_1_3_1_7843 12 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 181 255 (accept_3_5 11 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 181 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 181 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 255 (accept_3_5 8 181 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 181 255 (accept_3_5 5 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  181 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 181 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 181 255 (Polychromatic418967fa.accept_23_3_20_2_1_15603 3 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 255 (accept_3_5 2 181 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 181
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 180 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 180 255 15 5 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 180 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 74 180 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 180 255
  (Polychromatic418967fa.accept_19_16_9_8_1_11539 73 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 180 255 3 24 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 180 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 180 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 180 255 5 14 36 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 180 255 3 23 60 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 180 255
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 68 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 180 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 180 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 180 255 3 22 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 180 255 5 13 36 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 180 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 64 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 180 255 3 21 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 180 255 (Polychromatic418967fa.accept_13_10_11_8_1_1770 62 180 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 180 255
  (Polychromatic418967fa.accept_11_6_4_2_1_599 61 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 255 15 4 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 180 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 180 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 180 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 58
  180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 180 255 3 19 60 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 180 255
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 56 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 180 255 5 11 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 180 255 3 18 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 180 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 180 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 180 255
  (Polychromatic418967fa.accept_19_14_9_8_1_7271 52 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 180 255 3 17 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 180 255 5 10 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 180 255 (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 180 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 180 255 3 16 60 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 180 255
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 47 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 180 255 (Polychromatic418967fa.accept_16_14_4_15_1_3944 46 180 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 180 255 15 3 12 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 180 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 180 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 180 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 180 255 3 14 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 180 255
  (Polychromatic418967fa.accept_21_20_12_3_1_3387 41 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 180 255 5 8 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 180 255 3 13 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 180 255 (Polychromatic418967fa.accept_21_17_12_3_1_4848 38 180
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 180 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 255 3 12 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 180 255 5 7 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 180 255 (Polychromatic418967fa.accept_21_13_12_3_1_8028 34 180 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 180 255 3 11 60 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 180 255
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 32 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 180 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 180 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 180 255 15 2 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 180 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 255
  (Polychromatic418967fa.accept_11_6_4_2_1_599 28 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 180 255 3 9 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 180 255 (Polychromatic418967fa.accept_19_7_9_8_1_7297 26 180 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 180 255 5 5 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 180 255 3 8 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 180 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 22 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 180 255 3 7 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 180 255 5 4 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 180 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 180 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 180 255 3 6 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 180 255 (Polychromatic418967fa.accept_11_6_4_2_1_599
  17 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 180 255 15 1 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 180 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 180 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 255
  (Polychromatic418967fa.accept_21_13_12_3_1_8028 13 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 180 255 3 4 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 180 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 180 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 255 5 2 36 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 255 3 3 60 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 180 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 180 255 (Polychromatic418967fa.accept_19_7_9_8_1_7297 7 180 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 255 3 2 60 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 180 255 5 1 36 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 180 255 (Polychromatic418967fa.accept_13_4_11_8_1_1768 4 180 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 180 255 3 1 60 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 180 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 180 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 180 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 180 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 179 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 179 255 (accept_3_4 76 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 179 255 (Polychromatic418967fa.accept_16_11_3_15_1_1989 75 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 179 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 74
  179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 179 255 (accept_3_4 73
  179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 179 255
  (Polychromatic418967fa.accept_13_7_10_8_1_567 72 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 179 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 179 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 179 255 (accept_3_4 70 179 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 179 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 179 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68
  179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 179 255 (accept_3_4 67
  179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 179 255
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 66 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 179 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 179 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 179 255 (accept_3_4 64 179 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 179 255 (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 179 255 (accept_3_4 61 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 179 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 179 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 179 255 (accept_3_4 58 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 179 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 179 255 (accept_3_4 55 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 179 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 255 (Polychromatic418967fa.accept_23_7_18_2_1_15602 53 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 255 (accept_3_4 52 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 179 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 179 255 (accept_3_4 49 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 179 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 179 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 255 (accept_3_4 46 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 179 255 (accept_3_4 43 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 179 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 179 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 255 (accept_3_4 40 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 255 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 179 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 179 255 (accept_3_4 37 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 179 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 179 255 (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 255 (accept_3_4 34 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 179 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 255 (accept_3_4 31 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 255 (Polychromatic418967fa.accept_13_4_10_8_1_1817 30 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 255 (accept_3_4 28 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 255 (accept_3_4 25 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 255 (accept_3_4 22 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 255 (accept_3_4 19 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 255 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 255 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 255 (accept_3_4 16 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 179 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 255 (accept_3_4 13 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 255 (accept_3_4 10 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 179 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 255 (accept_3_4 7 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 255 (accept_3_4 4 179 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 255 (Polychromatic418967fa.accept_27_3_17_12_1_15601 3 179 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 255 (accept_3_4 1 179 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 178 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 178 255 (accept_3_5 77 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 178 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 178 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 178 255 (Polychromatic418967fa.accept_19_18_7_8_1_2112 75 178
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 178 255 (accept_3_5 74 178
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9
  73 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 178 255
  (Polychromatic418967fa.accept_10_2_8_5_1_587 72 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 178 255 (accept_3_5 71 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 178 255 (Polychromatic418967fa.accept_20_10_18_15_1_5359 70 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 178 255 (accept_3_5 68 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 178 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 178 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 178 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 178 255 (accept_3_5 65 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 178 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 178 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 178 255 (accept_3_5 62 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 178 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 178 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 60 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 178 255 (accept_3_5 59 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 178 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 178 255 (accept_3_5 56 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 178 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 178 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 178 255 (accept_3_5 53 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 178 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 52 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 178 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 178 255 (accept_3_5 50 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 178 255
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 178 255 (accept_3_5 47 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 178 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 178 255 (accept_3_5 44 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 178 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 178 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 178 255 (accept_3_5 41 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 178 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 178 255 (Polychromatic418967fa.accept_19_1_7_8_1_3262 39 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 178 255 (accept_3_5 38 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 178 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 178 255
  (Polychromatic418967fa.accept_20_16_18_15_1_11357 36 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 178 255 (accept_3_5 35 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 178 255 (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 178 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 178 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 178 255 (accept_3_5 32 178 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 178 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 178 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 178 255 (accept_3_5 29 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 178 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 178 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 178 255 (accept_3_5 26 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 178 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 178 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 178 255 (accept_3_5 23 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 178 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 178 255 (accept_3_5 20 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 178 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 178 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 178 255 (accept_3_5 17 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 178 255 (Polychromatic418967fa.accept_13_3_9_8_1_4202 16 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 178 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 178 255 (accept_3_5 14 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 178 255
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 178 255 (accept_3_5 11 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 178 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 255 (accept_3_5 8 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 178 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 178 255 (accept_3_5 5 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  178 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 178 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 178 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 255 (accept_3_5 2 178 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 178 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 177 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 177 255 3 26 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 177 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 177 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 177 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 76 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 177 255 3 25 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 177 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 177 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  73 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 177 255 3 24 59 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 177 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 177 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 177 255 3 23 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 177 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 68
  177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 177 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 177 255 3 22 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 177 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 65 177 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 255 (Polychromatic418967fa.accept_7_1_2_3_1_257
  64 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 177 255 3 21 59 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 177 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 177 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 177 255 3 20 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 177 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 177 255 3 19 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 177 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 177 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 255 (Polychromatic418967fa.accept_7_6_2_3_1_107
  55 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 177 255 3 18 59 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 177 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 177 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 177 255 3 17 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 177 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 177 255 3 16 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 177 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 177 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 177 255 3 15 59 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 177 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 177 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 177 255 3 14 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 177 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 177 255 3 13 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 177 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 177 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  37 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 177 255 3 12 59 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 177 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 177 255 3 11 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 177 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 177 255 3 10 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 177 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 177 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 177 255 3 9 59 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 255 3 8 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 177 255 3 7 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 177 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 177 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 255 3 6 59 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 255 3 5 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 177 255 3 4 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 177 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 255 3 3 59 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 255 3 2 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 177 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 177 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 177 255 3 1 59 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 177 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 177 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 176 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 176 255 (accept_3_4 79 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 176 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 176 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 176 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 176 255 (accept_3_4 76 176 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 176 255 (Polychromatic418967fa.accept_7_5_1_3_1_103
  75 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 176 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 176 255 (accept_3_4 73 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 176 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 176 255 (accept_3_4 70 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 176 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 176 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 176 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 176 255 (accept_3_4 67 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 176 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 176 255 (accept_3_4 64 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 176 255 (Polychromatic418967fa.accept_18_9_14_3_1_6407 63 176 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 176 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 176 255 (accept_3_4 61 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 176 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 176 255 (accept_3_4 58 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 176 255 (Polychromatic418967fa.accept_21_15_8_3_1_8086 57 176 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 176 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 176 255 (accept_3_4 55 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 176 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 176 255 (accept_3_4 52 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 176 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 176 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 176 255
  (Polychromatic418967fa.accept_19_12_5_8_1_7294 50 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 176 255 (accept_3_4 49 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 176 255 (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 176 255 (accept_3_4 46 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 176 255 (Polychromatic418967fa.accept_18_9_14_3_1_6407 45 176 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 176 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 176 255 (accept_3_4 43 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 176 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 176 255 (accept_3_4 40 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 176 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 176 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 176 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 176 255 (accept_3_4 37 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 176 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 176 255 (accept_3_4 34 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 176 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 176 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 176 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 176 255 (accept_3_4 31 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 176 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 255 (accept_3_4 28 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 176 255 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 176 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 176 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 176 255 (accept_3_4 25 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 176 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 176 255 (accept_3_4 22 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 176 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 176 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 176 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 176 255 (accept_3_4 19 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 176 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 176 255 (accept_3_4 16 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 176 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 176 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 176 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 176 255 (accept_3_4 13 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 176 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 255 (accept_3_4 10 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 176 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 176 255 (accept_3_4 7 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 255 (accept_3_4 4 176 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 255 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 176 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 255 (accept_3_4 1 176 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 175 255 (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 175 255 5 16 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 175 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 79 175 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 175 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 78 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 175 255 (accept_3_5 77 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 175 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 175 255 5 15 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 175 255 (accept_3_5 74 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 175 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 175 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 175 255 (Polychromatic418967fa.accept_19_15_4_8_1_7293 72 175
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 175 255 (accept_3_5 71 175
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 175 255 5 14 35 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 175 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 69 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 175 255 (accept_3_5 68 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 175 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 67 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 175 255 (Polychromatic418967fa.accept_13_1_6_8_1_208 66 175 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 175 255 5 13 35 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 175 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 175 255 (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 175 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 175 255 (accept_3_5 62 175 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 175 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 175 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 175 255 5 12 35 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 175 255 (accept_3_5 59 175 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 175 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 175 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 175 255 (accept_3_5 56 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  175 255 5 11 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 175 255 (Polychromatic418967fa.accept_13_2_6_8_1_1092 54 175 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 255 (accept_3_5 53 175 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 175 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 175 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 175 255 (Polychromatic418967fa.accept_9_6_4_3_1_203
  51 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 175 255 5 10 35 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 175 255
  (Polychromatic418967fa.accept_23_3_14_2_1_15600 49 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 255 (Polychromatic418967fa.accept_18_12_13_3_1_6427 48 175 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 255 (accept_3_5 47 175 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 175 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 175 255 5 9 35 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 175 255 (accept_3_5 44
  175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 175 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 175 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 255 (accept_3_5 41 175 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 175 255 5 8 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 175 255 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 175 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 255 (accept_3_5 38 175 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 175 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 255
  (Polychromatic418967fa.accept_19_17_4_8_1_4500 36 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 175 255 5 7 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 175 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 175 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 175 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 255 (accept_3_5 32 175 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 255
  (Polychromatic418967fa.accept_19_12_4_8_1_8768 31 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 175 255 5 6 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 175 255 (accept_3_5 29 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 175 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 175 255 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 175 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 255 (accept_3_5 26 175 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 175 255 5 5 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 175 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24
  175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 255 (accept_3_5 23
  175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 22 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 175 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 175 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 175 255 5 4 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 175 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 19
  175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 255
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 255 (accept_3_5 17 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 175 255 5 3 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 175 255 (accept_3_5 14 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 175 255 (Polychromatic418967fa.accept_19_13_4_8_1_11571 13 175 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 255 (Polychromatic418967fa.accept_11_1_10_2_1_58
  12 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 255 (accept_3_5 11
  175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 175 255 5 2 35 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 175 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 255 (accept_3_5 8 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 175 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 175 255 5 1 35 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 175 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4
  175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 255
  (Polychromatic418967fa.accept_19_3_4_8_1_8808 3 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 255 (accept_3_5 2 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 175 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 82 174 255 (Eq.refl Bool.true) (allA_succ_of_gcd 81 174 255 3 27 58 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 174 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 80 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 174 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 174 255 3 26 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 174 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77
  174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 174 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 76 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 174 255 3 25 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 174 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 174 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 174 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 174 255 3 24 58 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 174 255
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 71 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 174 255 (Polychromatic418967fa.accept_11_4_9_2_1_259 70 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 174 255 3 23 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 174 255 (Polychromatic418967fa.accept_12_8_6_3_1_366
  68 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 174 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 255 3 22 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 174 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 174 255 (Polychromatic418967fa.accept_12_4_6_3_1_332
  64 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 174 255 3 21 58 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 174 255
  (Polychromatic418967fa.accept_11_7_9_2_1_260 62 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 174 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 174 255 3 20 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 174 255 (Polychromatic418967fa.accept_10_9_4_5_1_616
  59 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 174 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 58 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 174 255 3 19 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 174 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 56 174 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 174 255 (Polychromatic418967fa.accept_13_3_5_8_1_1099
  55 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 174 255 3 18 58 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 174 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 174 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 174 255 3 17 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 174 255 (Polychromatic418967fa.accept_12_2_6_3_1_331
  50 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 174 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 255 3 16 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 255 (Polychromatic418967fa.accept_21_5_6_3_1_12580 47 174 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 174 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 46 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 174 255 3 15 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 174 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 174 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 174 255 (Polychromatic418967fa.accept_18_7_12_3_1_804
  43 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 174 255 3 14 58 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 174 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 174 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 174 255 3 13 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 174 255 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 255 3 12 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 255 (Polychromatic418967fa.accept_21_14_6_3_1_3382 35 174 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 174 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 174 255 3 11 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 174 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 174 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031
  31 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 174 255 3 10 58 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 174 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 174 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 174 255 3 9 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 174 255 (Polychromatic418967fa.accept_10_6_4_5_1_615
  26 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 255 3 8 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 174
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 174 255 3 7 58 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 174 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 174 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 174 255 3 6 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 174 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 174 255 3 5 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 174 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 174 255 3 4 58 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 174 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 174 255 3 3 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 174 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 174 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 255
  (Polychromatic418967fa.accept_11_7_9_2_1_260 7 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 255 3 2 58 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 174 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 174 255 3 1 58 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 174 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 174 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 174 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 173 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 173 255 (accept_3_4 82 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 173 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 173 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 173 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 173 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 173 255 (accept_3_4 79 173 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78
  173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 173 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 173 255 (accept_3_4 76 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 173 255 (Polychromatic418967fa.accept_13_10_4_8_1_2570 75 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 173 255 (accept_3_4 73 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 173 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 173 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 173 255 (accept_3_4 70 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 173 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 173 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 173 255 (accept_3_4 67 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 173 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 173 255 (accept_3_4 64 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 173 255 (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 173 255 (accept_3_4 61 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 173 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 173 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 173 255 (accept_3_4 58 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 173 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 173 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 173 255 (accept_3_4 55 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 173 255 (accept_3_4 52 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 173 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 255 (accept_3_4 49 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 255 (accept_3_4 46 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 173 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 255 (accept_3_4 43 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 255 (accept_3_4 40 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 255 (Polychromatic418967fa.accept_19_1_2_8_1_10129 39 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 255 (accept_3_4 37 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 255 (accept_3_4 34 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 255 (accept_3_4 31 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 255 (accept_3_4 28 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 255 (accept_3_4 25 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 255 (accept_3_4 22 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 255 (accept_3_4 19 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 255 (accept_3_4 16 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 255 (accept_3_4 13 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 255
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 255 (accept_3_4 10 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 255 (accept_3_4 7 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 173 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 255 (accept_3_4 4 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 255 (Polychromatic418967fa.accept_16_3_13_15_1_1913 3 173 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 255 (accept_3_4 1 173 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 172 255 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 172 255 (accept_3_5 83 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 172 255 (Polychromatic418967fa.accept_16_2_12_15_1_2908 82 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 172 255
  (Polychromatic418967fa.accept_21_18_4_3_1_8082 81 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 172 255 (accept_3_5 80 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 172 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 172 255 (accept_3_5 77 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 172 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 172 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 75 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 172 255 (accept_3_5 74 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 172 255 (Polychromatic418967fa.accept_13_7_3_8_1_1750 72 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 172 255 (accept_3_5 71 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 172 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 172 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 172 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 172 255 (accept_3_5 68 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 172 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 172 255 (accept_3_5 65 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 172 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 172 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 172 255
  (Polychromatic418967fa.accept_10_3_2_5_1_295 63 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 172 255 (accept_3_5 62 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 172 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 172 255 (accept_3_5 59 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 172 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 172 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 172 255 (accept_3_5 56 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 172 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 172 255 (accept_3_5 53 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 172 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 172 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 172 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 51 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 172 255 (accept_3_5 50 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 172 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 172 255 (accept_3_5 47 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 172 255 (Polychromatic418967fa.accept_13_7_3_8_1_1750 46 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 172 255
  (Polychromatic418967fa.accept_16_13_12_15_1_6290 45 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 172 255 (accept_3_5 44 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 172 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 172 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 172 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 172 255 (accept_3_5 41 172 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 172 255 (Polychromatic418967fa.accept_9_4_1_3_1_190
  40 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 172 255
  (Polychromatic418967fa.accept_21_18_4_3_1_8082 39 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 172 255 (accept_3_5 38 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 172 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 255 (accept_3_5 35 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 172 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 172 255 (accept_3_5 32 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 172 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 255 (accept_3_5 29 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 172
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 172 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 255 (accept_3_5 26 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 255 (accept_3_5 23 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 255
  (Polychromatic418967fa.accept_14_7_4_3_1_488 21 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 255 (accept_3_5 20 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 255 (accept_3_5 17 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 172 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 255 (accept_3_5 14 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 255 (Polychromatic418967fa.accept_19_12_1_8_1_4495 12 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 255 (accept_3_5 11 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 255 (Polychromatic418967fa.accept_20_10_12_15_1_3940 10
  172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 255
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 255 (accept_3_5 8 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 255 (accept_3_5 5 172 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 172 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 255 (accept_3_5 2 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 172 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 171 255 (Eq.refl Bool.true) (allA_succ_of_gcd 84 171 255 3 28 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 171 255
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 83 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 171 255 (Polychromatic418967fa.accept_24_10_3_15_1_15591 82 171 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 171 255 3 27 57 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 171 255
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 80 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 171 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 79 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 171 255 3 26 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 171 255
  (Polychromatic418967fa.accept_22_11_17_13_1_9270 77 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 171 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 76 171 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 171 255 3 25 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 171 255
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 74 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 171 255 (Polychromatic418967fa.accept_18_1_9_3_1_2672 73 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 171 255 3 24 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 171 255 (Polychromatic418967fa.accept_13_6_2_8_1_1782
  71 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 255
  (Polychromatic418967fa.accept_11_4_6_2_1_51 70 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 171 255 3 23 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 171 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 171 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 255
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 67 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 171 255 3 22 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 171 255 (Polychromatic418967fa.accept_16_1_11_15_1_498 65 171 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 255
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 64 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 171 255 3 21 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 171 255 (Polychromatic418967fa.accept_13_10_2_8_1_2603 62 171 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 255
  (Polychromatic418967fa.accept_18_7_9_3_1_800 61 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 171 255 3 20 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 171 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 59 171 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 255 (Polychromatic418967fa.accept_13_6_2_8_1_1782
  58 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 171 255 3 19 57 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 171 255
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 56 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 171 255 (Polychromatic418967fa.accept_16_7_11_15_1_2929 55 171 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 171 255 3 18 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 171 255
  (Polychromatic418967fa.accept_20_13_11_15_1_6881 53 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 171 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 171 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 171 255 3 17 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 171 255
  (Polychromatic418967fa.accept_18_14_9_3_1_6421 50 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 171 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 171 255 3 16 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 171 255
  (Polychromatic418967fa.accept_27_20_9_12_1_15599 47 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 171 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 46 171 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 171 255 3 15 57 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 171 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 171 255 (Polychromatic418967fa.accept_18_7_9_3_1_800 43 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 171 255 3 14 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 171 255
  (Polychromatic418967fa.accept_22_19_17_13_1_13939 41 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 171 255 (Polychromatic418967fa.accept_22_18_17_13_1_2923 40 171 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 171 255 3 13 57 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 171 255
  (Polychromatic418967fa.accept_18_2_9_3_1_3825 38 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 171 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 171 255 3 12 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 255
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 35 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 171 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 171 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 255 3 11 57 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 255
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 32 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 255 (Polychromatic418967fa.accept_18_13_9_3_1_5114 31 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 171 255 3 10 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 171 255 (Polychromatic418967fa.accept_10_9_1_5_1_594
  29 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 171 255 3 9 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 171 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 255 (Polychromatic418967fa.accept_18_7_9_3_1_800 25 171
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 255 3 8 57 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 255
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 23 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 255 (Polychromatic418967fa.accept_24_22_3_15_1_15598 22 171 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 255 3 7 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 255 3 6 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 255 (Polychromatic418967fa.accept_16_1_11_15_1_498
  17 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 255
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 171 255 3 5 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 171 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 255 (Polychromatic418967fa.accept_18_13_9_3_1_5114 13 171
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 255 3 4 57 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 255
  (Polychromatic418967fa.accept_22_11_17_13_1_9270 11 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 255 (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 171 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 255 3 3 57 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 255
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 8 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 255 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 255 3 2 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 255 (Polychromatic418967fa.accept_20_5_11_15_1_3920 5 171
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 171 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 171 255 3 1 57 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 171 255 (Polychromatic418967fa.accept_18_2_9_3_1_3825 2 171 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 255 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 171
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 170 255
  (Eq.refl Bool.true) (allA_succ_of_gcd 85 170 255 85 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 84 170 255 (Polychromatic418967fa.accept_13_6_1_8_1_1116 84 170 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 170 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 170 255 (accept_3_4 82 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 170 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 170 255 5 16 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 170 255 (accept_3_4 79 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 170 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 170 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 170 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 170 255 (accept_3_4 76 170 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 170 255 5 15 34 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 170 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 74 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 170 255 (accept_3_4 73 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 170 255 (Polychromatic418967fa.accept_13_7_1_8_1_1778 72 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 170 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 170 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 170 255 5 14 34 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 170 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 170 255 17 4 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 170 255 (accept_3_4 67 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 170 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 170 255 5 13 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 170 255 (accept_3_4 64 170 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 170 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 170 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 170 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 170 255 (accept_3_4 61 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  170 255 5 12 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 170 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 170 255 (accept_3_4 58 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 170 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 170 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 170 255 (Polychromatic418967fa.accept_9_2_8_3_1_181
  56 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 170 255 5 11 34 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 170 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 170 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 170 255 (accept_3_4 52 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 170 255 17 3 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 170 255 5 10 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 170 255 (accept_3_4 49 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 170 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 170 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 170 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47
  170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 170 255 (accept_3_4 46
  170 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 170 255 5 9 34 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 170 255
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 44 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 170 255 (accept_3_4 43 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 170 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 170 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 170 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 255 5 8 34 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 255
  (Polychromatic418967fa.accept_19_1_18_8_1_1066 39 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 170 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 170 255 (accept_3_4 37 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 170 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 170 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 170 255 5 7 34 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 170 255 17 2 10 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 170 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 170 255 (accept_3_4 31 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 170 255 5 6 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 170 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 170 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 170 255 (accept_3_4 28 170 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 170 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 170 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 170 255 5 5 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 170 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 170 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 170 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 255 (accept_3_4 22 170 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 170 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 170 255 5 4 34 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 170 255 (accept_3_4 19
  170 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 255
  (Polychromatic418967fa.accept_12_6_2_3_1_354 18 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 17 170 255 17 1 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 16 170 255 (accept_3_4 16 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 170 255 5 3 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 170 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 170 255 (accept_3_4 13 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 170 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 170 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 170 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 255 5 2 34 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 170 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 255 (accept_3_4 7 170 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 170 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 170 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 170 255 5 1 34 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 170 255 (accept_3_4 4 170 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 255 (Polychromatic418967fa.accept_20_3_10_15_1_620 3 170 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 255 (accept_3_4 1 170 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 169 255
  (Eq.refl Bool.true) (allA_succ_of_accept 86 169 255 (accept_3_5 86 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 169 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 85 169 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 169 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 169 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 169 255 (accept_3_5 83 169 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82
  169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 169 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 169 255 (accept_3_5 80 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 169 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 169 255 (accept_3_5 77 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 169 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 169 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 169 255 (accept_3_5 74 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 169 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 169 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 169 255 (accept_3_5 71 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 169 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 169 255 (accept_3_5 68 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 169 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 169 255 (accept_3_5 65 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 169 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 169 255
  (Polychromatic418967fa.accept_18_9_7_3_1_3871 63 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 169 255 (accept_3_5 62 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 169 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 169 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 169 255 (accept_3_5 59 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 57 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 255 (accept_3_5 56 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 255 (accept_3_5 53 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 255 (accept_3_5 50 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 169 255 (Polychromatic418967fa.accept_18_12_7_3_1_2666 48 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 255 (accept_3_5 47 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 169 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 255 (accept_3_5 44 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 255 (Polychromatic418967fa.accept_20_3_9_15_1_6847 43 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 255 (accept_3_5 41 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 255 (accept_3_5 38 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 255 (accept_3_5 35 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 169 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 255 (accept_3_5 32 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 255 (accept_3_5 29 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 255
  (Polychromatic418967fa.accept_18_9_7_3_1_3871 27 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 255 (accept_3_5 26 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 255 (accept_3_5 23 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 255 (accept_3_5 20 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 255 (accept_3_5 17 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 255 (accept_3_5 14 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 255 (accept_3_5 11 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 255 (accept_3_5 8 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 255 (Polychromatic418967fa.accept_21_7_1_3_1_11160 7 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 255 (accept_3_5 5 169 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 255
  (Polychromatic418967fa.accept_19_3_17_8_1_5916 3 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 255 (accept_3_5 2 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 169 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 88 168 255 (Eq.refl Bool.true) (allA_succ_of_gcd 87 168 255 3 29 56 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 86 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 168 255 3 28 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 83
  168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 82 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 168 255 3 27 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 168 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 80 168 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 168 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  79 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 168 255 3 26 56 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 168 255 3 25 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 74
  168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 73 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 168 255 3 24 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 168 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 71 168 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 168 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  70 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 168 255 3 23 56 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 68 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 168 255 3 22 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 65
  168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 168 255 3 21 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 168 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 168 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 168 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  61 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 168 255 3 20 56 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 168 255 3 19 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 55 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 255 3 18 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 168 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 168 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  52 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 168 255 3 17 56 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 168 255 3 16 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 47
  168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 168 255 3 15 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 168 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 44 168 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 168 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  43 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 255 3 14 56 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 168 255 3 13 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 255 3 12 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 168 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 168 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 255 (Polychromatic418967fa.accept_9_7_6_3_1_456
  34 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 168 255 3 11 56 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 255 3 10 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 168 255 3 9 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 168 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 168 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 255 3 8 56 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 168 255 3 7 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 20
  168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 255 3 6 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 168 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 168 255 3 5 56 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 255 3 4 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 168 255 3 3 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 168 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 168 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 255 3 2 56 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 168 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 168 255 3 1 56 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 168 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 168 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  89 167 255 (Eq.refl Bool.true) (allA_succ_of_accept 88 167 255 (accept_3_4 88 167 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 167 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 87 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 167 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 86
  167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 167 255 (accept_3_4 85
  167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 167 255
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 84 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 167 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 83 167 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 167 255 (accept_3_4 82 167 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 167 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 167 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 80
  167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 167 255 (accept_3_4 79
  167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 167 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 78 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 167 255 (Polychromatic418967fa.accept_19_1_15_8_1_4538 77 167 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 167 255 (accept_3_4 76 167 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 167 255 (Polychromatic418967fa.accept_13_10_11_8_1_1770 75 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 167 255 (accept_3_4 73 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 167 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 167 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 167 255 (accept_3_4 70 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 167 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 167 255 (accept_3_4 67 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 167 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 66 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 167 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 167 255 (accept_3_4 64 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 167 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 167 255 (accept_3_4 61 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 167 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 167 255 (Polychromatic418967fa.accept_16_11_7_15_1_1998 59 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 255 (accept_3_4 58 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 167
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 255 (accept_3_4 55 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 255 (Polychromatic418967fa.accept_16_6_7_15_1_1942 54 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 167 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 255 (accept_3_4 52 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 167 255 (accept_3_4 49 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 167 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 167 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 255 (accept_3_4 46 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 255 (accept_3_4 43 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 255 (Polychromatic418967fa.accept_19_3_15_8_1_3232 41 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 255 (accept_3_4 40 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 167 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 255 (accept_3_4 37 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 255 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 255 (accept_3_4 34 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 255 (accept_3_4 31 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 255 (accept_3_4 28 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 167 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 255 (accept_3_4 25 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 255 (accept_3_4 22 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 255 (accept_3_4 19 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 255 (accept_3_4 16 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 255 (accept_3_4 13 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 255 (accept_3_4 10 167 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 255 (accept_3_4 7 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 255 (Polychromatic418967fa.accept_20_5_7_15_1_2668 5 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 255 (accept_3_4 4 167 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 167 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 255 (accept_3_4 1 167 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 166 255
  (Eq.refl Bool.true) (allA_succ_of_accept 89 166 255 (accept_3_5 89 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 166 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 166 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 166 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 166 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 166 255 (accept_3_5 86 166 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 85
  166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 166 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 84 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 166 255 (accept_3_5 83 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 166 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 166 255 (accept_3_5 80 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 166 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 166 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 78 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 166 255 (accept_3_5 77 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 166 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 76 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 166 255 (Polychromatic418967fa.accept_14_5_12_3_1_3397 75 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 166 255 (accept_3_5 74 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 166 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 166 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 166 255 (accept_3_5 71 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 166 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 166 255 (accept_3_5 68 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 166 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 166 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 166 255 (accept_3_5 65 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 166 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 166 255 (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 166 255 (accept_3_5 62 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 166 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 166 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 166 255 (accept_3_5 59 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 166 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 166 255 (accept_3_5 56 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 166 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 166 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 166 255 (accept_3_5 53 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 166 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 166 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 166 255 (accept_3_5 50 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 166 255
  (Polychromatic418967fa.accept_21_6_19_3_1_4823 48 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 166 255 (accept_3_5 47 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 166 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 166 255 (accept_3_5 44 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 166 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 166 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 166 255 (accept_3_5 41 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 166 255 (Polychromatic418967fa.accept_19_2_14_8_1_3273 40 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 166 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 166 255 (accept_3_5 38 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 166 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 166 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 166 255 (accept_3_5 35 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 166 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 166 255 (accept_3_5 32 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 166 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 166 255 (accept_3_5 29 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 166 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 166 255 (Polychromatic418967fa.accept_21_6_19_3_1_4823 27 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 255 (accept_3_5 26 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 166 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 166 255 (accept_3_5 23 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 166 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 255 (accept_3_5 20 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 255 (accept_3_5 17 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 255 (accept_3_5 14 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 255
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 166 255 (accept_3_5 11 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 166 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 166 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 255 (accept_3_5 8 166 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 255 (accept_3_5 5 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 166 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 255 (accept_3_5 2 166 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 165 255
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 165 255 15 6 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 165 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 89 165 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 165 255
  (Polychromatic418967fa.accept_20_8_5_15_1_9868 88 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 165 255 3 29 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 165 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 165 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 165 255 5 17 33 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 165 255 3 28 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 165 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 83 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 165 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 165 255 3 27 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 165 255 5 16 33 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 165 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 79 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 165 255 3 26 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 165 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 165 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 165 255 (Polychromatic418967fa.accept_7_6_4_3_1_266
  76 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 165 255 15 5 11 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 165 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 165 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 73 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 165 255 3 24 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 165 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 71
  165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 165 255 5 14 33 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 165 255 3 23 55 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 165 255
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 68 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 165 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 165 255 3 22 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 165 255 5 13 33 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 165 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 64 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 165 255 3 21 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 165 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 165 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 255 (Polychromatic418967fa.accept_12_1_9_3_1_370
  61 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 165 255 15 4 11 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 165 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 165 255 3 19 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 165 255 (Polychromatic418967fa.accept_13_4_9_8_1_1736
  56 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 165 255 5 11 33 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 165 255 3 18 55
  85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 165 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 255 (Polychromatic418967fa.accept_16_4_5_15_1_5083 52 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 165 255 3 17 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 165 255 5 10 33 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 165 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 165 255 3 16 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 165 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 47 165 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 165 255 15 3 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 165 255 (Polychromatic418967fa.accept_19_6_13_8_1_4508 44 165 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 165 255 3 14 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 165 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 165 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 165 255 5 8 33 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 165 255 3 13 55 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 255 3 12 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 165 255 5 7 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 165 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 255 3 11 55 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 255
  (Polychromatic418967fa.accept_20_12_5_15_1_14100 32 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 165 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 165 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 255 15 2 11 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 255 (Polychromatic418967fa.accept_20_8_5_15_1_9868 28 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 255 3 9 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 165 255 5 5 33 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 165 255 3 8 55 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 165 255 3 7 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 165 255 5 4 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 165 255 (Polychromatic418967fa.accept_12_7_9_3_1_767
  19 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 255 3 6 55 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 255 (Polychromatic418967fa.accept_13_3_9_8_1_4202 16 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 255 15 1 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 165 255 3 4 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 165 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 165 255 5 2 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 165 255 3 3 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8
  165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 165 255 3 2 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 165 255 5 1 33 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 165 255 (Polychromatic418967fa.accept_13_4_9_8_1_1736 4 165 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 255 3 1 55 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 165 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 92 164 255 (Eq.refl Bool.true) (allA_succ_of_accept 91 164 255 (accept_3_4 91 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 164 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 164 255 (accept_3_4 88 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 164 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 164 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 86 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 164 255 (accept_3_4 85 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 164 255 (Polychromatic418967fa.accept_18_12_2_3_1_6414 84 164 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 164 255 (accept_3_4 82 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 164 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 164 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 80 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 164 255 (accept_3_4 79 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 164 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 164 255 (accept_3_4 76 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 164 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 164 255 (Polychromatic418967fa.accept_23_5_3_2_1_15597 74 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 164 255 (accept_3_4 73 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 164 255 (Polychromatic418967fa.accept_16_8_4_15_1_2941 72 164
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 164 255 (accept_3_4 70 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 164 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 164 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 68 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 164 255 (accept_3_4 67 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 164 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 164 255 (accept_3_4 64 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 164 255 (Polychromatic418967fa.accept_14_7_10_3_1_1034 63 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 164 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 164 255 (accept_3_4 61 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 164 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 164 255 (accept_3_4 58 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 164 255 (Polychromatic418967fa.accept_21_15_17_3_1_3373 57 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 164 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 56 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 164 255 (accept_3_4 55 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 164 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 164 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 164 255 (accept_3_4 52 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 164 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 164 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 164 255 (accept_3_4 49 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 164 255 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 164 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 164 255 (accept_3_4 46 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 164 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 164 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 164 255 (accept_3_4 43 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 164 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 164 255 (accept_3_4 40 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 164 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 164 255 (Polychromatic418967fa.accept_25_13_14_5_1_11984 38 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 164 255 (accept_3_4 37 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 164 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 164
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 164 255 (accept_3_4 34 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 164 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 164 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 164 255 (accept_3_4 31 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 164 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 164 255 (accept_3_4 28 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 164 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 164 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 164 255 (accept_3_4 25 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 164 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 164 255 (accept_3_4 22 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 164 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 164 255 (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 164 255 (accept_3_4 19 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 164 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 164 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 164 255 (accept_3_4 16 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 164 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 164 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 255 (accept_3_4 13 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 164 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 164 255 (accept_3_4 10 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  164 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 164 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 255 (accept_3_4 7 164 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 164 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 164 255 (accept_3_4 4 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  164 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 164 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 164 255 (Polychromatic418967fa.accept_20_2_4_15_1_6911 2 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 255 (accept_3_4 1 164 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 164
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 163 255
  (Eq.refl Bool.true) (allA_succ_of_accept 92 163 255 (accept_3_5 92 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 163 255 (Polychromatic418967fa.accept_16_11_3_15_1_1989 91 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 163 255 (Polychromatic418967fa.accept_7_6_2_3_1_107
  90 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 163 255 (accept_3_5 89
  163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 163 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 88 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 163 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 87 163 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 163 255 (accept_3_5 86 163 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 163 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 163 255 (Polychromatic418967fa.accept_8_4_3_7_1_491
  84 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 163 255 (accept_3_5 83
  163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 163 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 82 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 163 255 (Polychromatic418967fa.accept_11_4_9_2_1_259 81 163 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 163 255 (accept_3_5 80 163 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 163 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 79 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 163 255 (Polychromatic418967fa.accept_7_1_2_3_1_257
  78 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 163 255 (accept_3_5 77
  163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 163 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 76 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 163 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 163 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 163 255 (accept_3_5 74 163 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 163 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 73 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 163 255
  (Polychromatic418967fa.accept_10_2_3_5_1_996 72 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 163 255 (accept_3_5 71 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 163 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 163 255 (accept_3_5 68 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 163 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 255
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 66 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 163 255 (accept_3_5 65 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 163 255 (Polychromatic418967fa.accept_18_9_1_3_1_6451 63 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 255 (accept_3_5 62 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 163 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 163 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 163 255 (accept_3_5 59 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 255 (accept_3_5 56 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 255 (accept_3_5 53 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 255 (accept_3_5 50 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 255 (accept_3_5 47 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 255 (accept_3_5 44 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 163 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 255 (accept_3_5 41 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 255 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 255 (accept_3_5 38 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 163
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 255 (accept_3_5 35 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 255 (accept_3_5 32 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 255
  (Polychromatic418967fa.accept_18_12_1_3_1_7843 30 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 255 (accept_3_5 29 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 255 (accept_3_5 26 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 255 (accept_3_5 23 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 255 (accept_3_5 20 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 163 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 255
  (Polychromatic418967fa.accept_10_8_3_5_1_613 18 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 255 (accept_3_5 17 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 255 (accept_3_5 14 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 255 (accept_3_5 11 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 255 (accept_3_5 8 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 255 (accept_3_5 5 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 255 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 255 (accept_3_5 2 163 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 163 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 162
  255 (Eq.refl Bool.true) (allA_succ_of_gcd 93 162 255 3 31 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 162 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 92 162 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 162 255
  (Polychromatic418967fa.accept_21_7_15_3_1_8029 91 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 162 255 3 30 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 162 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 162 255 (Polychromatic418967fa.accept_7_4_1_3_1_277
  88 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 162 255 3 29 54 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 162 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 162 255 3 28 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 162 255 (Polychromatic418967fa.accept_10_3_2_5_1_295
  83 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 162 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 82 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 162 255 3 27 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 162 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 80 162 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 162 255 (Polychromatic418967fa.accept_7_2_1_3_1_102
  79 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 162 255 3 26 54 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 162 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 162 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 162 255 3 25 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 162 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 74
  162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 162 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 255 3 24 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 162 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 71 162 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 162 255 (Polychromatic418967fa.accept_12_10_6_3_1_786
  70 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 162 255 3 23 54 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 162 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 162 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 162 255 3 22 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65
  162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 162 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 64 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 162 255 3 21 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 162 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 62 162 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 162 255 3 20 54 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 162 255
  (Polychromatic418967fa.accept_19_2_10_8_1_3218 59 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 162 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 162 255 3 19 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 162 255 (Polychromatic418967fa.accept_12_8_6_3_1_366
  56 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 255
  (Polychromatic418967fa.accept_19_17_10_8_1_5942 55 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 162 255 3 18 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 162 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 162 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 162 255 3 17 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 162 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 162 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 162 255 3 16 54 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 162 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 162 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 162 255 3 15 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 162 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 255
  (Polychromatic418967fa.accept_10_3_2_5_1_295 43 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 255 3 14 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 162 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 255 (Polychromatic418967fa.accept_7_5_1_3_1_103
  40 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 162 255 3 13 54 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 162 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 162 255 3 12 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 162 255 (Polychromatic418967fa.accept_16_3_2_15_1_7367
  35 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 162 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 162 255 3 11 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 162 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 162 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 255
  (Polychromatic418967fa.accept_19_12_10_8_1_3270 31 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 162 255 3 10 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 162 255 3 9 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 162 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 162 255 3 8 54 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 162 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 162 255 3 7 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 162 255 (Polychromatic418967fa.accept_12_8_6_3_1_366
  20 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 255 3 6 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 162 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 162 255 3 5 54 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 162 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 162 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 255 3 4 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 162 255 3 3 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 162 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 162 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 255 3 2 54 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 162 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 162 255 3 1 54 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 162 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 162 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 162 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 95 161 255 (Eq.refl Bool.true) (allA_succ_of_accept 94 161 255 (accept_3_4 94 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 161 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 161 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 161 255 (accept_3_4 91 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 161 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 161 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 89 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 161 255 (accept_3_4 88 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 161 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 161 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 161 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 161 255 (accept_3_4 85 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 161 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 161 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 83 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 255 (accept_3_4 82 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 161 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 161 255 (accept_3_4 79 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 161 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 161 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 255 (accept_3_4 76 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 161 255 (accept_3_4 73 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 161 255 (Polychromatic418967fa.accept_16_8_1_15_1_1982 72 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 161 255 (Polychromatic418967fa.accept_19_14_9_8_1_7271 71 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 255 (accept_3_4 70 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 161 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 255 (accept_3_4 67 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 255 (accept_3_4 64 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 255 (Polychromatic418967fa.accept_22_19_7_13_1_6004 63 161 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 255 (accept_3_4 61 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 255 (accept_3_4 58 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 255 (accept_3_4 55 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 255 (accept_3_4 52 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 161 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 255 (accept_3_4 49 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 255 (Polychromatic418967fa.accept_21_6_14_3_1_4932 48 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 255 (accept_3_4 46 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 255 (accept_3_4 43 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 255 (accept_3_4 40 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 255 (accept_3_4 37 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 255 (Polychromatic418967fa.accept_19_16_9_8_1_11539 35 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 255 (accept_3_4 34 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 161 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 255 (accept_3_4 31 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 255 (accept_3_4 28 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 255 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 255 (accept_3_4 25 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 255 (accept_3_4 22 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 255 (accept_3_4 19 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 255 (Polychromatic418967fa.accept_19_17_9_8_1_3269 17 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 255 (accept_3_4 16 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 161 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 255 (accept_3_4 13 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 255 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 255 (accept_3_4 10 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 255 (accept_3_4 7 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 255 (accept_3_4 4 161 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 255 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 161 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 255 (accept_3_4 1 161 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 160
  255 (Eq.refl Bool.true) (allA_succ_of_gcd 95 160 255 5 19 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 160 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 94 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 160 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 93 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 160 255 (accept_3_5 92 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 160 255 5 18 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 160 255 (accept_3_5 89 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 160 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 160 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 160 255 (accept_3_5 86 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 160 255 5 17 32 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 160 255
  (Polychromatic418967fa.accept_22_18_6_13_1_7751 84 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 160 255 (accept_3_5 83 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 160 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 82 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 160 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 160 255 5 16 32 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 160 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 79 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 160 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 78 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 160 255 (accept_3_5 77 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 160 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 160 255 5 15 32 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 160 255 (accept_3_5 74 160 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 160 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 160 255 (accept_3_5 71 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  160 255 5 14 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 160 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 160 255 (accept_3_5 68 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 160 255 (Polychromatic418967fa.accept_12_6_4_3_1_361
  66 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 160 255 5 13 32 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 160 255
  (Polychromatic418967fa.accept_9_1_7_3_1_41 64 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 160 255 (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 160 255 (accept_3_5 62 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 160 255 5 12 32 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 160 255 (accept_3_5 59 160 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 160 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 160 255
  (Polychromatic418967fa.accept_23_11_22_2_1_15596 57 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 160 255 (accept_3_5 56 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 160 255 5 11 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 160 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 160 255 (accept_3_5 53 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 160 255 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 160 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 160 255 5 10 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 160 255 (Polychromatic418967fa.accept_11_4_6_2_1_51
  48 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 160 255 (accept_3_5 47
  160 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 160 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 46 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 160 255 5 9 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 160 255 (accept_3_5 44 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 160 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 160 255 (accept_3_5 41 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 160 255 5 8 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 160 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 160 255 (accept_3_5 38 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37
  160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 255
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 160 255 5 7 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 160 255 (Polychromatic418967fa.accept_23_11_22_2_1_15596 34 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 160 255 (Polychromatic418967fa.accept_9_6_7_3_1_436
  33 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 255 (accept_3_5 32
  160 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 31 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 255 5 6 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 160 255 (accept_3_5 29 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 255 (Polychromatic418967fa.accept_21_6_13_3_1_4851 27 160 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 255 (accept_3_5 26 160 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 160 255 5 5 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 160 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24
  160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 160 255 (accept_3_5 23
  160 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 160 255
  (Polychromatic418967fa.accept_9_4_7_3_1_43 22 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 160 255 (Polychromatic418967fa.accept_24_21_16_15_1_15547 21 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 255 5 4 32 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 160 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 160 255 (accept_3_5 17 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 160 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 160 255 5 3 32 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 160 255 (accept_3_5 14 160 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 255
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 255 (accept_3_5 11 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  160 255 5 2 32 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 160 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 160 255 (accept_3_5 8 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 160 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 160 255 5 1 32 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 160 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 160 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 160 255 (Polychromatic418967fa.accept_23_3_22_2_1_12322 3 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 255 (accept_3_5 2 160 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 160 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 159
  255 (Eq.refl Bool.true) (allA_succ_of_gcd 96 159 255 3 32 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 159 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 95 159 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 159 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 94 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 159 255 3 31 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 159 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 92 159 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  91 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 159 255 3 30 53 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 159 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 89 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 159 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 88 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 159 255 3 29 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 159 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 86
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 85 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 159 255 3 28 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 159 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 83 159 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 159 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  82 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 159 255 3 27 53 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 159 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 80 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 159 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 159 255 3 26 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 159 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 77
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 76 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 159 255 3 25 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 159 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 74 159 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  73 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 159 255 3 24 53 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 159 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 159 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 70 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 159 255 3 23 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 159 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 68
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 159 255 3 22 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 159 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 159 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 255 (Polychromatic418967fa.accept_7_1_5_3_1_268
  64 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 159 255 3 21 53 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 159 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 62 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 159 255 3 20 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 159 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 58 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 159 255 3 19 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 159 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 159 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  55 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 159 255 3 18 53 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 159 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 159 255 3 17 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 159 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 50
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 159 255 3 16 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 159 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 159 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 159 255 3 15 53 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 159 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 159 255 3 14 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 159 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 159 255 3 13 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 159 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 159 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 37
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 159 255 3 12 53 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 159 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 159 255 3 11 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 159 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 159 255 3 10 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 159 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 159 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 255 3 9 53 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 255 3 8 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 22 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 159 255 3 7 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 159 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 159 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 255 3 6 53 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 255 3 5 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 159 255 3 4 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 159 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 159 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 255 3 3 53 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 255 3 2 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 159 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 159 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 255 3 1 53 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 159 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 159 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  158 255 (Eq.refl Bool.true) (allA_succ_of_accept 97 158 255 (accept_3_4 97 158 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 158 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 96 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 158 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 95
  158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 158 255 (accept_3_4 94
  158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 158 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 158 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 92 158 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 158 255 (accept_3_4 91 158 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 158 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 158 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 89
  158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 158 255 (accept_3_4 88
  158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 158 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 87 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 158 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 86 158 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 158 255 (accept_3_4 85 158 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 158 255 (Polychromatic418967fa.accept_13_6_2_8_1_1782 84 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 158 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 158 255 (accept_3_4 82 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 158 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 158 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 80 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 158 255 (accept_3_4 79 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 158 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 158 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 158 255 (accept_3_4 76 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 158 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 75 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 158 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 74 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 158 255 (accept_3_4 73 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 158 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 158 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 158 255 (accept_3_4 70 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 158 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 158 255 (Polychromatic418967fa.accept_16_4_14_15_1_6331 68 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 158 255 (accept_3_4 67 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 158 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 158
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 158 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 158 255 (accept_3_4 64 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 158 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 158 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 158 255 (accept_3_4 61 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 158 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 158 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 158 255 (accept_3_4 58 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 158 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 158 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 158 255 (accept_3_4 55 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 158 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 158 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 158 255 (accept_3_4 52 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 158 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 158 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 158 255 (accept_3_4 49 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 158 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 158 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 158 255 (accept_3_4 46 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 158 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 158 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 44 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 158 255 (accept_3_4 43 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 158 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 158 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 158 255 (accept_3_4 40 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 158 255 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 158 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 158 255 (accept_3_4 37 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 158 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 158 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 158 255 (accept_3_4 34 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 158 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 158 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 32 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 158 255 (accept_3_4 31 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 158 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 158
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 158 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 158 255 (accept_3_4 28 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 158 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 158 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 255 (accept_3_4 25 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 158 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 158 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 158 255 (accept_3_4 22 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 158 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 158 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 255 (accept_3_4 19 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 158 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 158 255 (accept_3_4 16 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 158 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 158 255 (Polychromatic418967fa.accept_19_14_6_8_1_15595 14 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 255 (accept_3_4 13 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 158
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 158 255 (accept_3_4 10 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  158 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 158 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 255 (accept_3_4 7 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 158 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 158 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 158 255 (accept_3_4 4 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  158 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 158 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 158 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 255 (accept_3_4 1 158 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  157 255 (Eq.refl Bool.true) (allA_succ_of_accept 98 157 255 (accept_3_5 98 157 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 157 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 97 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 157 255 (Polychromatic418967fa.accept_9_6_4_3_1_203
  96 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 157 255 (accept_3_5 95
  157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 157 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 94 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 157 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 93 157 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 157 255 (accept_3_5 92 157 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 157 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 91 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 157 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 90
  157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 157 255 (accept_3_5 89
  157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 157 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 88 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 157 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 157 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 157 255 (accept_3_5 86 157 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 157 255 (Polychromatic418967fa.accept_13_7_1_8_1_1778 85 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 157 255
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 84 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 157 255 (accept_3_5 83 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 157 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 157 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 81 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 157 255 (accept_3_5 80 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 157 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 79 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 157 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 157 255 (accept_3_5 77 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 157 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 157 255 (Polychromatic418967fa.accept_21_12_10_3_1_11112 75 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 255 (accept_3_5 74 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 255
  (Polychromatic418967fa.accept_10_2_7_5_1_605 72 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 157 255 (accept_3_5 71 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 157 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 157 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 255 (accept_3_5 68 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 157 255 (accept_3_5 65 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 157 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 157 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 255 (accept_3_5 62 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 157 255 (accept_3_5 59 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 157 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 157 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 255 (accept_3_5 56 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 157 255 (accept_3_5 53 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 157 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 157 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 255 (accept_3_5 50 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 255 (Polychromatic418967fa.accept_21_7_10_3_1_1049 49 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 255
  (Polychromatic418967fa.accept_10_8_7_5_1_602 48 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 255 (accept_3_5 47 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 255 (accept_3_5 44 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 255 (accept_3_5 41 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 255 (Polychromatic418967fa.accept_20_19_17_15_1_2690 39 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 255 (accept_3_5 38 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 255
  (Polychromatic418967fa.accept_21_15_10_3_1_9578 36 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 157 255 (accept_3_5 35 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 157 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 255 (accept_3_5 32 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 255 (Polychromatic418967fa.accept_13_5_1_8_1_1115
  31 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 255 (accept_3_5 29 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 255 (Polychromatic418967fa.accept_18_9_13_3_1_5088 27 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 255 (accept_3_5 26 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 255 (accept_3_5 23 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 255 (accept_3_5 20 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 157 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 255 (accept_3_5 17 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 255 (accept_3_5 14 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 255
  (Polychromatic418967fa.accept_10_2_7_5_1_605 12 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 255 (accept_3_5 11 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 255 (accept_3_5 8 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 255 (accept_3_5 5 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 255 (accept_3_5 2 157 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 157 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  156 255 (Eq.refl Bool.true) (allA_succ_of_gcd 99 156 255 3 33 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 156 255 (Polychromatic418967fa.accept_16_2_12_15_1_2908 98 156
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 156 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 97 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 156 255 3 32 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 156 255 (Polychromatic418967fa.accept_22_7_2_13_1_15594 95 156 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 156 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 94 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 156 255 3 31 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 156 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 92 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 156 255 (Polychromatic418967fa.accept_8_3_4_7_1_475
  91 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 156 255 3 30 52 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 156 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 89 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 156 255 (Polychromatic418967fa.accept_16_8_12_15_1_2005 88 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 156 255 3 29 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 156 255
  (Polychromatic418967fa.accept_18_14_12_3_1_5103 86 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 156 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 156 255 3 28 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 156 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 83 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 156 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 156 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 156 255 3 27 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 156 255 (Polychromatic418967fa.accept_18_8_12_3_1_2708
  80 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 156 255
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 79 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 255 3 26 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 255 (Polychromatic418967fa.accept_16_13_12_15_1_6290 77 156 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 156 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 76 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 156 255 3 25 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 156 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 74 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 156 255
  (Polychromatic418967fa.accept_18_1_12_3_1_6426 73 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 255 3 24 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 156 255
  (Polychromatic418967fa.accept_19_13_4_8_1_11571 70 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 156 255 3 23 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 156 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 156 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 156 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 67 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 255 3 22 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 255 (Polychromatic418967fa.accept_20_5_16_15_1_3957 65 156 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 156 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 64 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 156 255 3 21 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 156 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 255 (Polychromatic418967fa.accept_7_5_2_3_1_106
  61 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 156 255 3 20 52 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 156 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 156 255 (Polychromatic418967fa.accept_20_18_16_15_1_3958 58 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 156 255 3 19 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 156 255
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 156 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 156 255 3 18 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 156 255
  (Polychromatic418967fa.accept_19_15_4_8_1_7293 53 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 156 255 (Polychromatic418967fa.accept_16_4_12_15_1_6289 52 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 156 255 3 17 52 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 156 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 156 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 156 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 156 255 3 16 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 156 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 255
  (Polychromatic418967fa.accept_27_19_21_12_1_15593 46 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 156 255 3 15 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 156 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 44 156 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 255 3 14 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 255 (Polychromatic418967fa.accept_7_5_2_3_1_106
  40 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 156 255 3 13 52 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 156 255
  (Polychromatic418967fa.accept_18_2_12_3_1_2707 38 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 156 255 (Polychromatic418967fa.accept_18_1_12_3_1_6426 37 156 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 156 255 3 12 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 156 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 35
  156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 156 255 3 11 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 156 255 (Polychromatic418967fa.accept_18_14_12_3_1_5103 32 156 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 255
  (Polychromatic418967fa.accept_10_1_6_5_1_304 31 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 255 3 10 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 156 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 255 (Polychromatic418967fa.accept_19_9_4_8_1_8805
  28 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 156 255 3 9 52 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 156 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 156 255 (Polychromatic418967fa.accept_18_7_12_3_1_804 25 156 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 255 3 8 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 255 (Polychromatic418967fa.accept_21_2_9_3_1_4841
  23 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 156 255 3 7 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 156 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 156 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 156 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 255 3 6 52 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 255
  (Polychromatic418967fa.accept_19_17_4_8_1_4500 17 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 156 255 (Polychromatic418967fa.accept_21_16_9_3_1_6436 16 156 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 156 255 3 5 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 156 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 14
  156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 255 3 4 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 156 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 156 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 255 (Polychromatic418967fa.accept_19_10_4_8_1_11500 10 156
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 156 255 3 3 52 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 156 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 156 255 (Polychromatic418967fa.accept_18_7_12_3_1_804 7 156 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 255 3 2 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 156 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 4 156 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 156 255 3 1 52 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 156 255 (Polychromatic418967fa.accept_16_2_12_15_1_2908 2 156 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 156 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 155 255 (Eq.refl Bool.true) (allA_succ_of_gcd 100 155 255 5 20 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 155 255
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 99 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 155 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 98 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 155 255 (accept_3_4 97 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 155 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 155 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 155 255 5 19 31 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 155 255 (accept_3_4 94 155 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 155 255 (Polychromatic418967fa.accept_7_2_1_3_1_102
  93 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 155 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 155 255 (accept_3_4 91 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90
  155 255 5 18 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 155 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 155 255 (accept_3_4 88 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 155 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 155 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 86
  155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 155 255 5 17 31 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 155 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 84 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 155 255 (Polychromatic418967fa.accept_13_5_12_8_1_198 83 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 155 255 (accept_3_4 82 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 155 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 155 255 5 16 31 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 155 255 (accept_3_4 79 155 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 155 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 155 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 155 255 (accept_3_4 76 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  155 255 5 15 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 155 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 255 (accept_3_4 73 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 155 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 255 (Polychromatic418967fa.accept_9_8_2_3_1_447
  71 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 155 255 5 14 31 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 155 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 69 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 155 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 255 (accept_3_4 67 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 155 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818 66 155 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 155 255 5 13 31 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 155 255 (accept_3_4 64 155 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 255 (Polychromatic418967fa.accept_19_6_3_8_1_7283
  63 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 255 (accept_3_4 61 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  155 255 5 12 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 155 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 255 (accept_3_4 58 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 155 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 155 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 155 255 5 11 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 155 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 255 (Polychromatic418967fa.accept_7_4_1_3_1_277
  53 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 255 (accept_3_4 52
  155 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 155 255 5 10 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 155 255 (accept_3_4 49 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 155 255 (Polychromatic418967fa.accept_13_9_12_8_1_570 48 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 155 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 255 (accept_3_4 46 155 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 155 255 5 9 31 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 155 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 255 (accept_3_4 43 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 155 255 5 8 31 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 155 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 155 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 255 (accept_3_4 37 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 155 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 155 255 5 7 31 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 155 255 (accept_3_4 34 155 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 155 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 255 (accept_3_4 31 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  155 255 5 6 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 155 255 (Polychromatic418967fa.accept_23_6_17_2_1_10701 29 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 155 255 (accept_3_4 28 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 155 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 155 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 155 255 5 5 31 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 155 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 24 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 155 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 255 (accept_3_4 22 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 155 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 155 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 155 255 5 4 31 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 155 255 (accept_3_4 19 155 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 255 (Polychromatic418967fa.accept_7_4_1_3_1_277
  18 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 255 (accept_3_4 16 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  155 255 5 3 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 155 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 155 255 (accept_3_4 13 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 155 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 155 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 155 255 5 2 31 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 155 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 155 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 255 (accept_3_4 7 155 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 155 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 155 255 5 1 31 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 155 255 (accept_3_4 4 155 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 155 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 255 (accept_3_4 1 155 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 154 255 (Eq.refl Bool.true) (allA_succ_of_accept 101 154 255 (accept_3_5 101 154 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 154 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 100 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 154 255
  (Polychromatic418967fa.accept_10_9_4_5_1_616 99 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 154 255 (accept_3_5 98 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 154 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 96 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 154 255 (accept_3_5 95 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 154 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 94 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 154 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 154 255 (accept_3_5 92 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 154 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 154 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 90 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 154 255 (accept_3_5 89 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 154 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 88 154 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 154 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 87 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 154 255 (accept_3_5 86 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 154 255 (Polychromatic418967fa.accept_13_6_11_8_1_1111 84 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 154 255 (accept_3_5 83 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 154 255 (Polychromatic418967fa.accept_13_4_11_8_1_1768 82 154
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 154 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 154 255 (accept_3_5 80 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 154 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 154 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 154 255 (accept_3_5 77 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 154 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 76 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 154 255
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 75 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 154 255 (accept_3_5 74 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 154 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 154 255 (Polychromatic418967fa.accept_19_15_2_8_1_7263 72 154
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 154 255 (accept_3_5 71 154
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 154 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 70 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 154 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 154 255 (accept_3_5 68 154 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 154 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 154 255 (Polychromatic418967fa.accept_10_6_4_5_1_615
  66 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 154 255 (accept_3_5 65
  154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 154 255
  (Polychromatic418967fa.accept_21_1_7_3_1_6450 64 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 154 255 (Polychromatic418967fa.accept_19_6_2_8_1_4496 63 154 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 154 255 (accept_3_5 62 154 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 154 255 (Polychromatic418967fa.accept_9_6_1_3_1_191
  60 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 154 255 (accept_3_5 59
  154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 154 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 58 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 154 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 154 255 (accept_3_5 56 154 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 154 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 154 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 154 255 (accept_3_5 53 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 154 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 154 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 255 (accept_3_5 50 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 154 255
  (Polychromatic418967fa.accept_13_9_11_8_1_195 48 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 154 255 (accept_3_5 47 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 154 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 154 255 (accept_3_5 44 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 154 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 154 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 154 255 (accept_3_5 41 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 154 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 154 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 154 255 (accept_3_5 38 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 154 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 154 255 (accept_3_5 35 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 154 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 255 (accept_3_5 32 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 154 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 154 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 154 255 (accept_3_5 29 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 154 255 (Polychromatic418967fa.accept_20_8_14_15_1_6932 28 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 154 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 154 255 (accept_3_5 26 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 154 255 (accept_3_5 23 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 255 (accept_3_5 20 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 255 (accept_3_5 17 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 255 (accept_3_5 14 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 255
  (Polychromatic418967fa.accept_21_12_7_3_1_4927 12 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 154 255 (accept_3_5 11 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 154 255 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 255 (accept_3_5 8 154 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 255 (accept_3_5 5 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 154 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 255 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 255 (accept_3_5 2 154 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 153 255 (Eq.refl Bool.true) (allA_succ_of_gcd 102 153 255 51 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 153 255 (Polychromatic418967fa.accept_12_5_9_3_1_85
  101 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 100 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 153 255 3 33 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 153 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 153 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 255 (Polychromatic418967fa.accept_10_7_3_5_1_301
  97 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 153 255 3 32 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 153 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 95 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 153 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 153 255 3 31 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 153 255 (Polychromatic418967fa.accept_10_2_3_5_1_996
  92 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 91 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 153 255 3 30 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 153 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 89 153 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 255 (Polychromatic418967fa.accept_7_4_6_3_1_271
  88 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 153 255 3 29 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 153 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 153 255 17 5 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 153 255 3 28 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 153 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 83 153 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 82 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 153 255 3 27 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 153 255 (Polychromatic418967fa.accept_13_2_10_8_1_1126 80 153 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 153 255 3 26 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 153 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 77 153 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 255
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 76 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 153 255 3 25 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 153 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 153 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 73 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 153 255 3 24 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 153 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 71 153 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 153 255 3 23 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 68 153 255 17 4 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 153 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 153 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 153 255 3 22 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 153 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 153 255 (Polychromatic418967fa.accept_13_12_10_8_1_3343 64 153 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 153 255 3 21 51 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 153 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 153 255 3 20 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 153 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  59 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 153 255 3 19 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 153 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 56 153 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 255 (Polychromatic418967fa.accept_12_7_9_3_1_767
  55 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 153 255 3 18 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 153 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 153 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 153 255 51 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 153 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 153 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 153 255 3 16 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 153 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 153 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 153 255 3 15 51 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 153 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 153 255 3 14 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 255
  (Polychromatic418967fa.accept_16_8_9_15_1_5112 40 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 255 3 13 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 153 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 255 (Polychromatic418967fa.accept_7_2_6_3_1_100
  37 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 153 255 3 12 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 153 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 153 255 17 2 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 153 255 3 11 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 153 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 153 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 255 (Polychromatic418967fa.accept_12_7_9_3_1_767
  31 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 255 3 10 51 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 255 3 9 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 153 255 3 8 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 153 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 255 3 7 51 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 255
  (Polychromatic418967fa.accept_13_7_10_8_1_567 20 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 255 3 6 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 153 255 17 1 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 153 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16
  153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 255 3 5 51 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 255 3 4 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 11
  153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 153 255 3 3 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 153 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 153 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 255 3 2 51 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 153 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 255 3 1 51 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 255
  (Polychromatic418967fa.accept_11_1_10_2_1_58 1 153 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 153
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 152 255 (Eq.refl Bool.true) (allA_succ_of_accept 103 152 255 (accept_3_4 103 152 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 152 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 102 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 101 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 152 255 (accept_3_4 100 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 152 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 152 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 98 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 152 255 (accept_3_4 97 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 152 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 152 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 152 255 (accept_3_4 94 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 152 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 152 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 92 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 152 255 (accept_3_4 91 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 152 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 152 255 (accept_3_4 88 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 152 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 152 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 152 255 (accept_3_4 85 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 152 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 84 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 152 255 (accept_3_4 82 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 152 255 (Polychromatic418967fa.accept_11_4_9_2_1_259 81 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 152 255 (Polychromatic418967fa.accept_23_11_14_2_1_13877 80 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 152 255 (accept_3_4 79 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 152 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 152 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 77 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 152 255 (accept_3_4 76 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 152 255 (Polychromatic418967fa.accept_14_5_12_3_1_3397 75 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 152 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 74 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 152 255 (accept_3_4 73 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 152 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 152 255 (accept_3_4 70 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 152 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 152 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 68 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 152 255 (accept_3_4 67 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 152 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 152 255 (accept_3_4 64 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 152 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 152 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 62 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 152 255 (accept_3_4 61 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 152 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 152 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 152 255 (accept_3_4 58 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 152 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 152 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 56 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 152 255 (accept_3_4 55 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 152 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 152 255 (accept_3_4 52 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 152 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 152 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 152 255 (accept_3_4 49 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 152 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 152 255 (accept_3_4 46 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 152 255 (Polychromatic418967fa.accept_18_9_8_3_1_2702 45 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 152 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 152 255 (accept_3_4 43 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 152 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 152 255 (accept_3_4 40 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 152 255 (Polychromatic418967fa.accept_16_7_8_15_1_6327 39 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 152 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 152 255 (accept_3_4 37 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 152 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 152 255 (accept_3_4 34 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 152 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 152 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 152 255 (accept_3_4 31 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 152 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 152 255 (accept_3_4 28 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 152 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 152 255 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 152 255 (accept_3_4 25 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 152 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 152 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 152 255 (accept_3_4 22 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 152 255 (Polychromatic418967fa.accept_22_21_20_13_1_15592 21 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 255 (accept_3_4 19 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 152 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 152
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 152 255 (accept_3_4 16 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 152 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 152 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 255 (accept_3_4 13 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 152 255 (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 152 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 152 255 (accept_3_4 10 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  152 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 152 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 255 (accept_3_4 7 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 152 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 152 255 (accept_3_4 4 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  152 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 152 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 152 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 255 (accept_3_4 1 152 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 151 255 (Eq.refl Bool.true) (allA_succ_of_accept 104 151 255 (accept_3_5 104 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 151 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 103 151
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 151 255
  (Polychromatic418967fa.accept_16_6_7_15_1_1942 102 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 151 255 (accept_3_5 101 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 100 151 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 151 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 151 255 (accept_3_5 98 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 151 255 (Polychromatic418967fa.accept_7_6_4_3_1_266
  97 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 151 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 96 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 151 255 (accept_3_5 95 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 151 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 93 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 151 255 (accept_3_5 92 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 151 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 91 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 151 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 90 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 151 255 (accept_3_5 89 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 151 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 151 255 (accept_3_5 86 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 151 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 151 255
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 151 255 (accept_3_5 83 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 151 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 81 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 151 255 (accept_3_5 80 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 151 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 79 151
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 151 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 151 255 (accept_3_5 77 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 151 255 (Polychromatic418967fa.accept_16_11_7_15_1_1998 75 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 255 (accept_3_5 74 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 151 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 255
  (Polychromatic418967fa.accept_16_8_7_15_1_6339 72 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 151 255 (accept_3_5 71 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 151 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 255 (accept_3_5 68 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 255
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 66 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 255 (accept_3_5 65 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 255 (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 255 (accept_3_5 62 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 255 (Polychromatic418967fa.accept_19_4_18_8_1_10117 61 151
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 60 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 151 255 (accept_3_5 59 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 151 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 255 (accept_3_5 56 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 255
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 255 (accept_3_5 53 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 255 (accept_3_5 50 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 255 (accept_3_5 47 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 255 (accept_3_5 44 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 255 (accept_3_5 41 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 255 (accept_3_5 38 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 255 (accept_3_5 35 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 255 (accept_3_5 32 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 255
  (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 151 255 (accept_3_5 29 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 151 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 255 (accept_3_5 26 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 255
  (Polychromatic418967fa.accept_20_5_11_15_1_3920 25 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 255 (accept_3_5 23 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 255 (accept_3_5 20 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 255 (Polychromatic418967fa.accept_21_18_4_3_1_8082 18 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 255 (accept_3_5 17 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 255 (accept_3_5 14 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 255 (Polychromatic418967fa.accept_18_12_7_3_1_2666 12 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 255 (accept_3_5 11 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 151 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 255 (accept_3_5 8 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 255 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 255 (accept_3_5 5 151 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 255
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 255 (accept_3_5 2 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 151 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 150 255 (Eq.refl Bool.true) (allA_succ_of_gcd 105 150 255 15 7 10 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 150 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 104 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 150 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 103 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 150 255 3 34 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 101
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 150 255 5 20 30 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 150 255 3 33 50 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 150 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 98 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 255 3 32 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 150 255 5 19 30 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 150 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 94 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 150 255 3 31 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 150 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 92 150 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 150 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  91 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 150 255 15 6 10 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 150 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 150 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 88 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 150 255 3 29 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 150 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 86
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 150 255 5 17 30 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 150 255 3 28 50 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 150 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 82 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 150 255 3 27 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 150 255 5 16 30 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 79 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 255 3 26 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 150 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 150 255 (Polychromatic418967fa.accept_9_4_6_3_1_179
  76 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 150 255 15 5 10 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 150 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 74 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 255 3 24 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 71
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 255 5 14 30 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 150 255 3 23 50 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 150 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 68 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 150 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 255 3 22 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 150 255 5 13 30 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 150 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 150 255 3 21 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 150 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 150 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 150 255 15 4 10 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 150 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 150 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 150 255 3 19 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 150 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 150 255 5 11 30 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 150 255 3 18 50 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 150 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 150 255 3 17 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 150 255 5 10 30 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 255 3 16 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 150 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 255 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 150 255 15 3 10 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 150 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 150 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 255 3 14 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 255 5 8 30 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 150 255 3 13 50 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 150 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 255 3 12 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 150 255 5 7 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 150 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 34
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 150 255 3 11 50 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 150 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 255 15 2 10 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 150 255 3 9 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 150 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 150 255 5 5 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 150 255 3 8 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 150 255 3 7 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 150 255 5 4 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 150 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 255 3 6 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 150 255 15 1 10 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 150 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 150 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 255 3 4 50 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 255 5 2 30 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 150 255 3 3 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 150 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 150 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 255 3 2 50 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 150 255 5 1 30 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 150 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 150 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 150 255 3 1 50 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 150 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 150 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 149 255 (Eq.refl Bool.true) (allA_succ_of_accept 106 149 255 (accept_3_4 106 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 149 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 105 149
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 149 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 149 255 (accept_3_4 103 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 149 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 149 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 101 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 149 255 (accept_3_4 100 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 149 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 149 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 149 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 149 255 (accept_3_4 97 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 149 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 149 255 (Polychromatic418967fa.accept_22_7_17_13_1_10962 95 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 149 255 (accept_3_4 94 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 149 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 93 149
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 149 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 149 255 (accept_3_4 91 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 149 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 149 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 149 255 (accept_3_4 88 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 149 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 87 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 149 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 149 255 (accept_3_4 85 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 149 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 149 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 255 (accept_3_4 82 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 149 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 149 255 (accept_3_4 79 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 149 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 149 255 (Polychromatic418967fa.accept_19_1_16_8_1_10075 77 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 255 (accept_3_4 76 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 149 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 149 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 149 255 (accept_3_4 73 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 149 255 (Polychromatic418967fa.accept_19_15_16_8_1_11553 72 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 255 (accept_3_4 70 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 149 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 149 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 149 255 (accept_3_4 67 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 149 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 149 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 65 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 255 (accept_3_4 64 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 149 255 (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 149 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 255 (accept_3_4 61 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 59 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 255 (accept_3_4 58 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 255 (accept_3_4 55 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 255 (accept_3_4 52 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 255 (accept_3_4 49 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 255 (accept_3_4 46 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 255 (accept_3_4 43 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 255 (accept_3_4 40 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 255 (Polychromatic418967fa.accept_19_1_16_8_1_10075 39 149 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 255 (accept_3_4 37 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 255 (accept_3_4 34 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 255 (accept_3_4 31 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 255 (accept_3_4 28 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 255 (accept_3_4 25 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 255 (Polychromatic418967fa.accept_20_3_9_15_1_6847 23 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 255 (accept_3_4 22 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 149 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 255 (accept_3_4 19 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 255 (accept_3_4 16 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 255 (accept_3_4 13 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 255 (accept_3_4 10 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 255 (accept_3_4 7 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 255 (accept_3_4 4 149 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 255 (Polychromatic418967fa.accept_20_3_9_15_1_6847 3 149 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 255 (accept_3_4 1 149 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 148 255 (Eq.refl Bool.true) (allA_succ_of_accept 107 148 255 (accept_3_5 107 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 148 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 106 148
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 148 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 105 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 148 255 (accept_3_5 104 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 148 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 148 255 (accept_3_5 101 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 148 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 148
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 148 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 99 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 148 255 (accept_3_5 98 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 97 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 148 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 148 255 (accept_3_5 95 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 148 255 (Polychromatic418967fa.accept_13_3_5_8_1_1099 94 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 148 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 148 255 (accept_3_5 92 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 148 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 90 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 148 255 (accept_3_5 89 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 148 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 148 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 148 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 87 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 148 255 (accept_3_5 86 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 148 255 (Polychromatic418967fa.accept_22_18_16_13_1_10902 84 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 148 255 (accept_3_5 83 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 148 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 148 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 148 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 148 255 (accept_3_5 80 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 148 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 148 255 (accept_3_5 77 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 148 255 (Polychromatic418967fa.accept_16_12_4_15_1_5091 76 148 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 148 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 148 255 (accept_3_5 74 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 148 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 148 255 (accept_3_5 71 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 148 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 148 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 69 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 148 255 (accept_3_5 68 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 148 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 148 255 (accept_3_5 65 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 148 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 148 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 148 255
  (Polychromatic418967fa.accept_10_3_8_5_1_606 63 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 148 255 (accept_3_5 62 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 148 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 148 255 (accept_3_5 59 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 148 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 148 255
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 148 255 (accept_3_5 56 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 148 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 148 255 (accept_3_5 53 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 148 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 148 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 148 255 (accept_3_5 50 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 148 255 (Polychromatic418967fa.accept_21_6_1_3_1_3399 48 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 148 255 (accept_3_5 47 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 148 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 148 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 148 255
  (Polychromatic418967fa.accept_19_7_15_8_1_1089 45 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 148 255 (accept_3_5 44 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 148 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 148 255 (accept_3_5 41 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 148 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 148 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 148 255 (accept_3_5 38 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 148 255 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 148 255 (accept_3_5 35 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 148 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 148 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 148 255 (accept_3_5 32 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 148 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 148 255 (accept_3_5 29 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 148 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 148 255 (accept_3_5 26 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 148 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 148 255 (accept_3_5 23 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 148 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 255
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 148 255 (accept_3_5 20 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 148 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 255 (accept_3_5 17 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 148 255 (accept_3_5 14 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 148 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 255 (accept_3_5 11 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 148 255 (accept_3_5 8 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 148 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 255 (accept_3_5 5 148 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 148 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 148 255 (accept_3_5 2 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  148 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 148
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 147 255 (Eq.refl Bool.true) (allA_succ_of_gcd 108 147 255 3 36 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 147 255
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 107 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 147 255 (Polychromatic418967fa.accept_24_10_3_15_1_15591 106 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 147 255 3 35 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 147 255
  (Polychromatic418967fa.accept_19_9_14_8_1_11549 104 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 147 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 103 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 147 255 3 34 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 147 255
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 101 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 147 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 100 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 147 255 3 33 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 147 255
  (Polychromatic418967fa.accept_10_8_7_5_1_602 98 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 147 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 97 147 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 147 255 3 32 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 147 255 (Polychromatic418967fa.accept_14_11_7_3_1_3416
  95 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 255
  (Polychromatic418967fa.accept_11_6_4_2_1_599 94 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 147 255 3 31 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 147 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 92 147 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 255
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 91 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 147 255 3 30 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 147 255 (Polychromatic418967fa.accept_13_11_4_8_1_1098 89 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 255
  (Polychromatic418967fa.accept_10_8_7_5_1_602 88 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 147 255 3 29 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 147 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 86 147 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 255
  (Polychromatic418967fa.accept_19_9_14_8_1_11549 85 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 147 255 3 28 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 147 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 83 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 255
  (Polychromatic418967fa.accept_10_2_7_5_1_605 82 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 147 255 3 27 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 147 255 (Polychromatic418967fa.accept_14_10_7_3_1_1022 80 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 255
  (Polychromatic418967fa.accept_19_3_14_8_1_3272 79 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 147 255 3 26 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 147 255 (Polychromatic418967fa.accept_13_12_4_8_1_1120 77 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 76 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 147 255 3 25 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 147 255 (Polychromatic418967fa.accept_13_9_4_8_1_1752 74 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 255
  (Polychromatic418967fa.accept_10_3_7_5_1_288 73 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 147 255 3 24 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 147 255 (Polychromatic418967fa.accept_16_7_3_15_1_2940 71 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 255
  (Polychromatic418967fa.accept_19_13_14_8_1_4490 70 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 147 255 3 23 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 147 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 255
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 67 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 147 255 3 22 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 147 255 (Polychromatic418967fa.accept_20_5_7_15_1_2668 65 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 255
  (Polychromatic418967fa.accept_11_9_4_2_1_600 64 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 147 255 3 21 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 147 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 62 147 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 255 (Polychromatic418967fa.accept_11_6_4_2_1_599
  61 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 147 255 3 20 49 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 147 255
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 59 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 147 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 58 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 147 255 3 19 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 147 255
  (Polychromatic418967fa.accept_25_6_22_5_1_15590 56 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 147 255 (Polychromatic418967fa.accept_16_7_3_15_1_2940 55 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 147 255 3 18 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 147 255
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 147 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 147 255 3 17 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 147 255 (Polychromatic418967fa.accept_11_6_4_2_1_599
  50 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 255
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 147 255 3 16 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 147 255 (Polychromatic418967fa.accept_19_9_14_8_1_11549 47 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 255
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 46 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 147 255 3 15 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 147 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 147 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 255 (Polychromatic418967fa.accept_10_3_7_5_1_288
  43 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 147 255 3 14 49 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 147 255
  (Polychromatic418967fa.accept_19_3_14_8_1_3272 41 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 255 (Polychromatic418967fa.accept_19_2_14_8_1_3273 40 147 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 255 3 13 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 255 (Polychromatic418967fa.accept_10_8_7_5_1_602
  38 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 255
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 37 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 147 255 3 12 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 147 255 (Polychromatic418967fa.accept_13_9_4_8_1_1752 35 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 255
  (Polychromatic418967fa.accept_16_2_3_15_1_6309 34 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 255 3 11 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 147 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 255 (Polychromatic418967fa.accept_11_9_4_2_1_600
  31 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 255 3 10 49 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 255
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 29 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 147 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 147 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 147 255 3 9 49 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 255
  (Polychromatic418967fa.accept_19_7_14_8_1_4535 26 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 255 (Polychromatic418967fa.accept_13_12_4_8_1_1120 25 147 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 255 3 8 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 255 (Polychromatic418967fa.accept_10_3_7_5_1_288
  23 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 255
  (Polychromatic418967fa.accept_10_2_7_5_1_605 22 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 147 255 3 7 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 147 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 147 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 255 (Polychromatic418967fa.accept_25_19_22_5_1_15589 19
  147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 255 3 6 49 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 255
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 255 (Polychromatic418967fa.accept_23_16_9_2_1_9078 16 147 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 255 3 5 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 255
  (Polychromatic418967fa.accept_22_14_15_13_1_10826 14 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 147 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 147 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 255 3 4 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 255
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 255 (Polychromatic418967fa.accept_13_10_4_8_1_2570 10 147 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 255 3 3 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 147 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 255
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 147 255 3 2 49 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 147 255 (Polychromatic418967fa.accept_19_5_14_8_1_5944 5 147 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 147 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 255 3 1 49 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 255
  (Polychromatic418967fa.accept_10_2_7_5_1_605 2 147 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 255 (Polychromatic418967fa.accept_20_1_7_15_1_1521 1 147 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 147
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 146 255 (Eq.refl Bool.true) (allA_succ_of_accept 109 146 255 (accept_3_4 109 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 146 255 (Polychromatic418967fa.accept_14_10_6_3_1_1055 108
  146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 146 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 107 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 146 255 (accept_3_4 106 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 146 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 146 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 104 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 146 255 (accept_3_4 103 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 146 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 146
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 146 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 146 255 (accept_3_4 100 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 146 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 99 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 146 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 98 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 146 255 (accept_3_4 97 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 146 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 96 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 146 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 95 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 146 255 (accept_3_4 94 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 146 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 146 255 (Polychromatic418967fa.accept_16_12_2_15_1_490 92 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 146 255 (accept_3_4 91 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 146 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 146
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 146 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 146 255 (accept_3_4 88 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 146 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 146 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 86 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 146 255 (accept_3_4 85 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 146 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 84 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 146 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 146 255 (accept_3_4 82 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 146 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 146 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 80 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 146 255 (accept_3_4 79 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 146 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 146 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 146 255 (accept_3_4 76 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 146 255 (Polychromatic418967fa.accept_19_18_13_8_1_10099 75 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 74 146 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 146 255 (accept_3_4 73 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 146 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 146 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 146 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 146 255 (accept_3_4 70 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 146 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 146 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 68 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 146 255 (accept_3_4 67 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 146 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 146 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 146 255 (accept_3_4 64 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 146 255 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 146 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 62 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 146 255 (accept_3_4 61 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 146 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 146 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 146 255 (accept_3_4 58 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 146 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 146 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 146 255 (accept_3_4 55 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 146 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 146 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 146 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 146 255 (accept_3_4 52 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 146 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 146 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 146 255 (accept_3_4 49 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 146 255 (Polychromatic418967fa.accept_13_9_3_8_1_573 48 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 146 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 146 255 (accept_3_4 46 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 146 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 146 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 146 255 (accept_3_4 43 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 146 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 146 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 146 255 (accept_3_4 40 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 146 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 146 255 (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 146 255 (accept_3_4 37 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 146 255 (Polychromatic418967fa.accept_27_9_11_12_1_15588 36
  146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 146 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 146 255 (accept_3_4 34 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 146 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 146 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 146 255 (accept_3_4 31 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 146 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 146 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 146 255 (accept_3_4 28 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 146 255 (Polychromatic418967fa.accept_18_9_2_3_1_5082 27 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 146 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 146 255 (accept_3_4 25 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 146 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 146 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 146 255 (accept_3_4 22 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 146 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 146 255 (Polychromatic418967fa.accept_13_7_3_8_1_1750 20 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 255 (accept_3_4 19 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 146 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 146 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 146 255 (accept_3_4 16 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 146 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 146 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 255 (accept_3_4 13 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 146 255 (accept_3_4 10 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  146 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 146 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 255 (accept_3_4 7 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 146 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 146 255 (accept_3_4 4 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  146 255 (Polychromatic418967fa.accept_16_3_2_15_1_7367 3 146 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 146 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 255 (accept_3_4 1 146 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 146
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 145 255 (Eq.refl Bool.true) (allA_succ_of_gcd 110 145 255 5 22 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 145 255
  (Polychromatic418967fa.accept_20_9_5_15_1_3965 109 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 145 255 (Polychromatic418967fa.accept_20_8_5_15_1_9868 108 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 145 255 (accept_3_5 107 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 106 145
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 145 255 5 21 29 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 145 255 (accept_3_5
  104 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 145 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 103 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 145 255 (accept_3_5 101 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 145 255 5 20 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 145 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 145 255 (accept_3_5 98 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 145 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 97 145 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 145 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 96 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 95 145 255 5 19 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 94 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 145 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 93
  145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 145 255 (accept_3_5 92
  145 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 145 255
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 91 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 145 255 5 18 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 145 255 (accept_3_5 89 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 145 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 87 145 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 145 255 (accept_3_5 86 145 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 145 255 5 17 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 145 255
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 84 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 145 255 (accept_3_5 83 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 145 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 81 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 145 255 5 16 29 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 145 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 79 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 255 (accept_3_5 77 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 145 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 145 255 5 15 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 145 255 (accept_3_5 74 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 145 255 (Polychromatic418967fa.accept_20_13_5_15_1_8431 73 145
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 255 (accept_3_5 71 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  145 255 5 14 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 145 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 255 (accept_3_5 68 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 145 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 145 255 5 13 29 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 145 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 145 255 (Polychromatic418967fa.accept_18_9_1_3_1_6451 63 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 255 (accept_3_5 62 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 145 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 145 255 5 12 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 145 255 (accept_3_5 59 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 145 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 255 (accept_3_5 56 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  145 255 5 11 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 255 (accept_3_5 53 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 145 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 51
  145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 145 255 5 10 29 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 145 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 145 255 (Polychromatic418967fa.accept_18_12_1_3_1_7843 48 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 255 (accept_3_5 47 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 145 255 5 9 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 145 255 (accept_3_5 44 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 145 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 255 (accept_3_5 41 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  145 255 5 8 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 145 255 (Polychromatic418967fa.accept_19_1_12_8_1_8799 39 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 145 255 (accept_3_5 38 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 145 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 145 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 145 255 5 7 29 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 145 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 145 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 255 (accept_3_5 32 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 145 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 255 5 6 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 255 (accept_3_5 29 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 145 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 255
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 145 255 (accept_3_5 26 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 145 255 5 5 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 145 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 255 (accept_3_5 23 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 255 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 145 255 5 4 29 51
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 145 255
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 255 (accept_3_5 17 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 145 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 145 255 5 3 29 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 145 255 (accept_3_5 14 145 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 145 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 255
  (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 255 (accept_3_5 11 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  145 255 5 2 29 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 145 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 145 255 (accept_3_5 8 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 145 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 145 255 5 1 29 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 255 (Polychromatic418967fa.accept_20_3_5_15_1_2644 3 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 255 (accept_3_5 2 145 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 144 255 (Eq.refl Bool.true) (allA_succ_of_gcd 111 144 255 3 37 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 144 255
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 110 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 144 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 109 144 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 144 255 3 36 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 144 255
  (Polychromatic418967fa.accept_19_12_11_8_1_2091 107 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 144 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 144 255 3 35 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 144 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 104 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 144 255 (Polychromatic418967fa.accept_13_12_1_8_1_1779 103 144 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 144 255 3 34 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 144 255
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 101 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 144 255 (Polychromatic418967fa.accept_13_9_1_8_1_1742 100 144 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 144 255 3 33 48 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 144 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 98 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 144 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 144 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 144 255 3 32 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 255
  (Polychromatic418967fa.accept_21_11_18_3_1_4862 95 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 144 255 (Polychromatic418967fa.accept_19_18_11_8_1_10080 94 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 144 255 3 31 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 144 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 92 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 144 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 91 144 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 144 255 3 30 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 144 255 (Polychromatic418967fa.accept_10_9_4_5_1_616
  89 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 144 255
  (Polychromatic418967fa.accept_19_12_11_8_1_2091 88 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 87 144 255 3 29 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 86 144 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 86 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 144 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 85 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 255 3 28 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 144 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 144 255
  (Polychromatic418967fa.accept_20_2_4_15_1_6911 82 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 144 255 3 27 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 144 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 80 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 144 255
  (Polychromatic418967fa.accept_10_9_4_5_1_616 79 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 255 3 26 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 255 (Polychromatic418967fa.accept_13_12_1_8_1_1779 77 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 144 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 76 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 144 255 3 25 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 144 255 (Polychromatic418967fa.accept_13_9_1_8_1_1742 74 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 144 255
  (Polychromatic418967fa.accept_19_16_11_8_1_8758 73 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 144 255 3 24 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 144 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 144 255
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 70 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 144 255 3 23 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 144 255 (Polychromatic418967fa.accept_21_5_18_3_1_4908 68 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 255
  (Polychromatic418967fa.accept_19_10_11_8_1_10121 67 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 144 255 3 22 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 144 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 144 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 64 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 144 255 3 21 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 144 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 144 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031
  61 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 144 255 3 20 48 85
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 144 255
  (Polychromatic418967fa.accept_10_9_4_5_1_616 59 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 144 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 144 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 144 255 3 19 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 144 255 (Polychromatic418967fa.accept_10_6_4_5_1_615
  56 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 255 3 18 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 255 (Polychromatic418967fa.accept_21_11_18_3_1_4862 53 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 255
  (Polychromatic418967fa.accept_21_10_18_3_1_11147 52 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 144 255 3 17 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 144 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 255
  (Polychromatic418967fa.accept_10_9_4_5_1_616 49 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 255 3 16 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 46 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 144 255 3 15 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 144 255 (Polychromatic418967fa.accept_13_5_1_8_1_1115 44 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 255 3 14 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 144 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 255
  (Polychromatic418967fa.accept_19_2_11_8_1_2090 40 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 144 255 3 13 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 144 255 (Polychromatic418967fa.accept_13_12_1_8_1_1779 38 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 255
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 37 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 255 3 12 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 255 (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 144 255 3 11 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 144 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 255
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 255 3 10 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 144 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 255
  (Polychromatic418967fa.accept_19_9_11_8_1_10050 28 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 144 255 3 9 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 144 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 255
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 255 3 8 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 255 (Polychromatic418967fa.accept_21_2_18_3_1_9697 23 144 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 144 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 144 255 3 7 48 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 144 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 144 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 144 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 255 3 6 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 255
  (Polychromatic418967fa.accept_19_17_11_8_1_11490 17 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 144 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 144 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 144 255 3 5 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 144 255
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 144 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 144 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 255 3 4 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031
  11 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 144 255 3 3 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 144 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 144 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 255 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 144 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 255 3 2 48 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 255
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 255 (Polychromatic418967fa.accept_21_4_18_3_1_11175 4 144 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 144 255 3 1 48 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 144 255 (Polychromatic418967fa.accept_19_2_11_8_1_2090 2 144 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 143 255 (Eq.refl Bool.true) (allA_succ_of_accept 112 143 255 (accept_3_4 112 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 143 255 (Polychromatic418967fa.accept_19_16_10_8_1_10067 111
  143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 110 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 143 255 (accept_3_4 109 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 143 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 108 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 143 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 107 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 143 255 (accept_3_4 106 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 105 143
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 104 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 143 255 (accept_3_4 103 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 143 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 102 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 143 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 101 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 143 255 (accept_3_4 100 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 143 255 (Polychromatic418967fa.accept_19_4_10_8_1_11508 99 143
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 98 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 143 255 (accept_3_4 97 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 143 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 95 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 143 255 (accept_3_4 94 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 143 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 93 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 143 255 (accept_3_4 91 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 143 255 (Polychromatic418967fa.accept_20_10_3_15_1_1546 90 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 143 255 (Polychromatic418967fa.accept_20_9_3_15_1_3929 89 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 143 255 (accept_3_4 88 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 143 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 143 255 (accept_3_4 85 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 143 255 (Polychromatic418967fa.accept_25_9_18_5_1_4647 84 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 143 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 83 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 143 255 (accept_3_4 82 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 143 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 143 255 (accept_3_4 79 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 143 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 255 (accept_3_4 76 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 143 255 (Polychromatic418967fa.accept_19_18_10_8_1_2088 75 143 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 74 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 143 255 (accept_3_4 73 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 143 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 143 255 (Polychromatic418967fa.accept_21_8_17_3_1_8031 71 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 255 (accept_3_4 70 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 143 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 143 255 (accept_3_4 67 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 143 255 (Polychromatic418967fa.accept_23_20_5_2_1_12294 66 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 143 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 255 (accept_3_4 64 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 255 (Polychromatic418967fa.accept_22_19_11_13_1_10981 63 143 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 143 255 (accept_3_4 61 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 143 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 255 (accept_3_4 58 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 255 (accept_3_4 55 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 255 (Polychromatic418967fa.accept_19_16_10_8_1_10067 54 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 255 (Polychromatic418967fa.accept_22_9_11_13_1_10890 53 143 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 255 (accept_3_4 52 143 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183
  51 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 255 (accept_3_4 49 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 255 (accept_3_4 46 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 255 (accept_3_4 43 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 255 (accept_3_4 40 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 255 (Polychromatic418967fa.accept_21_18_17_3_1_4906 39 143 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 255 (accept_3_4 37 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 255 (Polychromatic418967fa.accept_19_17_10_8_1_5942 36 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 255 (Polychromatic418967fa.accept_19_16_10_8_1_10067 35 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 255 (accept_3_4 34 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 143 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 255 (accept_3_4 31 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 255 (Polychromatic418967fa.accept_19_11_10_8_1_7256 30 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 255 (accept_3_4 28 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 255 (accept_3_4 25 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 255 (accept_3_4 22 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 255 (accept_3_4 19 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 255 (accept_3_4 16 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 143 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 255 (accept_3_4 13 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 255 (accept_3_4 10 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 255 (accept_3_4 7 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 255 (accept_3_4 4 143 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 255 (Polychromatic418967fa.accept_22_3_11_13_1_9262 3 143 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 255 (accept_3_4 1 143 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 142 255 (Eq.refl Bool.true) (allA_succ_of_accept 113 142 255 (accept_3_5 113 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 142 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 112 142
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 142 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 111 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 142 255 (accept_3_5 110 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 109 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 142 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 108 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 142 255 (accept_3_5 107 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 142 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 106 142
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 142 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 142 255 (accept_3_5 104 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 142 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 103 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 142 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 102 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 142 255 (accept_3_5 101 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 142 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 100 142
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 142 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 142 255 (accept_3_5 98 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 142 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 142 255 (accept_3_5 95 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 142 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 94 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 142 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 142 255 (accept_3_5 92 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 142 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 142 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 142 255 (accept_3_5 89 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 142 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 88 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 142 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 87 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 142 255 (accept_3_5 86 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 142 255 (Polychromatic418967fa.accept_16_4_14_15_1_6331 84 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 142 255 (accept_3_5 83 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 142 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 142 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 142 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 142 255 (accept_3_5 80 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 142 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 142 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 142 255 (accept_3_5 77 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 142 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 142 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 142 255 (accept_3_5 74 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 142 255 (Polychromatic418967fa.accept_13_7_12_8_1_199 72 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 142 255 (accept_3_5 71 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 142 255 (Polychromatic418967fa.accept_13_5_12_8_1_198 70 142
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 142 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 142 255 (accept_3_5 68 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 142 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 142 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 142 255 (accept_3_5 65 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 142 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 142 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 142 255
  (Polychromatic418967fa.accept_10_3_2_5_1_295 63 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 142 255 (accept_3_5 62 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 142 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 142 255 (accept_3_5 59 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 142 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 142 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 142 255 (accept_3_5 56 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 142 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 142 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 142 255 (accept_3_5 53 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 142 255 (Polychromatic418967fa.accept_16_4_14_15_1_6331 52 142 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 142 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 142 255 (accept_3_5 50 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 142 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 142 255 (accept_3_5 47 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 142 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 142 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 142 255 (accept_3_5 44 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 142 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 142 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 142 255 (accept_3_5 41 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 142 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 142 255
  (Polychromatic418967fa.accept_16_7_14_15_1_2932 39 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 142 255 (accept_3_5 38 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 142 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 142 255 (accept_3_5 35 142 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 142 255 (Polychromatic418967fa.accept_7_6_2_3_1_107
  34 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 142 255 (accept_3_5 32 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 142 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 142 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 142 255 (accept_3_5 29 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 142 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 142 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 142 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 142 255 (accept_3_5 26 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 142 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 142 255 (accept_3_5 23 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 142 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 142 255 (accept_3_5 20 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 142 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 142 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 142 255 (accept_3_5 17 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 142 255 (Polychromatic418967fa.accept_19_16_9_8_1_11539 16 142
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 142 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 142 255 (accept_3_5 14 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 142 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 142 255 (accept_3_5 11 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 142 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 142 255 (accept_3_5 8 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  142 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 142 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 255 (accept_3_5 5 142 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 142 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 142 255
  (Polychromatic418967fa.accept_10_3_2_5_1_295 3 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 142 255 (accept_3_5 2 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  142 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 142
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_255_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))


