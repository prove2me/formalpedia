-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_237
-- name    : RealPinwheel_FiveSixths_WitnessD8_237
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:20:58.360207+00:00
-- url     : https://prove2.me/theorems/a6b2d107-7341-4784-b164-63d5a6f2188f
-- title:
--   Exact witness block D8_237
-- statement:
--   These exact witnesses represent words 3228 through 3261 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 3228–3261; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_237_3227 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (4))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (6))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (4))) (.branch 29 (.leaf (3)) (.leaf (1)))))))
  code := certificateD8_3227
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-21)))),
  (.branch 7 (.leaf (0)) (.branch 29 (.leaf (-2)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-12)) (.leaf (-13)))),
  (.branch 13 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 13 (.leaf (-21)) (.branch 26 (.leaf (-20)) (.leaf (-17)))) (.branch 28 (.leaf (-14)) (.branch 29 (.leaf (-11)) (.leaf (-8))))),
  (.leaf (-5)),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 23 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.leaf (-8)))) (.branch 27 (.branch 26 (.leaf (-7)) (.leaf (-6))) (.branch 28 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3))))))]
def witnessD8_237_3228 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (6))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (2)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (7)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (3)))))))
  code := certificateD8_3228
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-9)) (.leaf (-10)))),
  (.branch 22 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.leaf (-10)) (.leaf (-9))),
  (.branch 22 (.leaf (-10)) (.branch 29 (.leaf (-9)) (.leaf (-7)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.branch 4 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_237_3229 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (3))) (.branch 10 (.leaf (6)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (7)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (1)))))))
  code := certificateD8_3229
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-20)) (.leaf (-33)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 22 (.leaf (-4)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 16 (.leaf (-12)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-11)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 8 (.branch 4 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 24 (.branch 20 (.leaf (-29)) (.leaf (-28))) (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-20)) (.leaf (-13)))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 28 (.leaf (-1)) (.leaf (0))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 17 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-10)))) (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-11))) (.branch 29 (.leaf (-8)) (.leaf (-5)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 15 (.branch 12 (.branch 11 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16))))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_237_3230 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (3))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (5)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (2)) (.leaf (1)))))))
  code := certificateD8_3230
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-20)) (.leaf (-33)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 22 (.leaf (-4)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 16 (.leaf (-12)) (.leaf (-13)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 16 (.branch 8 (.branch 4 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 24 (.branch 20 (.leaf (-29)) (.leaf (-28))) (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-20)) (.leaf (-13)))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 28 (.leaf (-1)) (.leaf (0))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 17 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-10)))) (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 21 (.branch 5 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_237_3231 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (7)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (7)) (.leaf (2)))))))
  code := certificateD8_3231
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1))]
def witnessD8_237_3232 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (5)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (7))) (.branch 21 (.leaf (0)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (3)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (5)) (.leaf (2)))))))
  code := certificateD8_3232
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-25))),
  (.branch 20 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 27 (.branch 18 (.leaf (-11)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-25)) (.branch 7 (.leaf (-24)) (.leaf (-23)))) (.branch 9 (.leaf (-22)) (.branch 10 (.leaf (-21)) (.leaf (-20))))) (.branch 14 (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17)))) (.branch 15 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-14)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_237_3233 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (2))) (.branch 14 (.leaf (5)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (2))) (.branch 29 (.leaf (5)) (.leaf (1)))))))
  code := certificateD8_3233
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-23))),
  (.branch 22 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 18 (.branch 12 (.branch 9 (.branch 8 (.leaf (-23)) (.leaf (-22))) (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19))))) (.branch 15 (.branch 13 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))))) (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_237_3234 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (5)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (6)))))))
  code := certificateD8_3234
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 28 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_237_3235 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (6))) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (7)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (4)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (7))) (.branch 21 (.leaf (2)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (6)) (.leaf (5)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (4)) (.leaf (7)))))))
  code := certificateD8_3235
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 26 (.branch 24 (.leaf (-14)) (.branch 25 (.leaf (-12)) (.leaf (-10)))) (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 29 (.leaf (-4)) (.leaf (-2))),
  (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD8_237_3236 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (7))) (.branch 21 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (4))) (.branch 29 (.leaf (1)) (.leaf (2)))))))
  code := certificateD8_3236
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.branch 21 (.branch 5 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_237_3237 : CycleWitness 8 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (2)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (3)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (7)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (3)) (.leaf (1)))))))
  code := certificateD8_3237
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-19))),
  (.branch 26 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 24 (.branch 20 (.leaf (-14)) (.leaf (-13))) (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-19)) (.leaf (-18))) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-14))) (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))))) (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_237_3238 : CycleWitness 8 where
  length := 29
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (6)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (7)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (0))) (.branch 21 (.leaf (6)) (.leaf (1))))) (.branch 25 (.branch 23 (.leaf (3)) (.branch 24 (.leaf (0)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (1)) (.leaf (7)))))))
  code := certificateD8_3238
  counts := ![(.branch 12 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 14 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-20))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-16)))),
  (.leaf (0))]
  high := ![(.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 11 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-5))))),
  (.branch 18 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.branch 14 (.branch 4 (.leaf (-20)) (.leaf (-19))) (.branch 24 (.leaf (-18)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-20)) (.leaf (-18))) (.branch 22 (.leaf (-16)) (.branch 23 (.leaf (-14)) (.leaf (-12))))) (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-16)) (.leaf (-14))) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD8_237_3239 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (7)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (5))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (1)))))))
  code := certificateD8_3239
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 24 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))),
  (.branch 15 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 16 (.leaf (-17)) (.branch 21 (.leaf (-21)) (.leaf (-24))))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-10)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-19))),
  (.branch 23 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-24))),
  (.branch 20 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 25 (.branch 22 (.leaf (-24)) (.leaf (-22))) (.branch 28 (.leaf (-20)) (.leaf (-13)))),
  (.branch 19 (.branch 5 (.leaf (-20)) (.branch 12 (.leaf (-19)) (.leaf (-18)))) (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-10))) (.branch 28 (.leaf (-3)) (.leaf (0))))),
  (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.leaf (-3)) (.leaf (-2))),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-19)) (.leaf (-18))) (.branch 13 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.branch 15 (.leaf (-15)) (.leaf (-14))) (.branch 17 (.leaf (-13)) (.branch 18 (.leaf (-12)) (.leaf (-11)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-10)) (.leaf (-9))) (.branch 22 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-6))))) (.branch 26 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-24)) (.branch 7 (.leaf (-23)) (.leaf (-22)))) (.branch 9 (.leaf (-21)) (.branch 10 (.leaf (-20)) (.leaf (-19))))) (.branch 14 (.branch 12 (.leaf (-18)) (.branch 13 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-13)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-12)) (.branch 19 (.leaf (-11)) (.leaf (-10)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-9)) (.leaf (-8))) (.branch 23 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_237_3240 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (7)) (.leaf (3)))))))
  code := certificateD8_3240
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.leaf (-11)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-11)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 16 (.branch 7 (.branch 4 (.leaf (-28)) (.leaf (-27))) (.branch 10 (.leaf (-26)) (.branch 13 (.leaf (-25)) (.leaf (-24))))) (.branch 22 (.branch 19 (.leaf (-23)) (.leaf (-22))) (.branch 25 (.leaf (-21)) (.branch 28 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 15 (.branch 3 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17)))) (.branch 27 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-6)) (.leaf (-4))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-15)) (.leaf (-13)))) (.branch 27 (.leaf (-11)) (.branch 28 (.leaf (-9)) (.leaf (-7))))),
  (.branch 25 (.branch 23 (.branch 8 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-14)) (.leaf (-13)))) (.branch 19 (.branch 18 (.leaf (-12)) (.leaf (-11))) (.branch 20 (.leaf (-10)) (.leaf (-9))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-7))) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_237_3241 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (5)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (7)) (.leaf (3)))))))
  code := certificateD8_3241
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 25 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 19 (.leaf (-10)) (.branch 27 (.leaf (-12)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 13 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 28 (.leaf (-13)) (.leaf (-9))),
  (.branch 22 (.branch 12 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.branch 25 (.branch 5 (.leaf (-17)) (.branch 15 (.leaf (-16)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 19 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.branch 25 (.branch 9 (.leaf (-13)) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 21 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-16)) (.branch 23 (.leaf (-14)) (.leaf (-12))))) (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-14)) (.leaf (-13)))) (.branch 19 (.branch 18 (.leaf (-12)) (.leaf (-11))) (.branch 20 (.leaf (-10)) (.leaf (-9))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-7))) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_237_3242 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (7)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (2)))))))
  code := certificateD8_3242
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-8)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-24))),
  (.branch 20 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 24 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 14 (.leaf (-3)) (.leaf (-2))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-24)) (.branch 7 (.leaf (-23)) (.leaf (-22)))) (.branch 9 (.leaf (-21)) (.branch 10 (.leaf (-20)) (.leaf (-19))))) (.branch 14 (.branch 12 (.leaf (-18)) (.branch 13 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-13)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-12)) (.branch 19 (.leaf (-11)) (.leaf (-10)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-9)) (.leaf (-8))) (.branch 23 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_237_3243 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (3)))))))
  code := certificateD8_3243
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-21))) (.branch 16 (.leaf (-22)) (.branch 23 (.leaf (-23)) (.leaf (-24))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 18 (.leaf (-14)) (.branch 25 (.leaf (-15)) (.leaf (-16))))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 20 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-24)))]
  high := ![(.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 24 (.leaf (-24)) (.branch 25 (.leaf (-20)) (.leaf (-16)))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-8)) (.leaf (-4))))),
  (.branch 27 (.branch 26 (.leaf (-16)) (.leaf (-12))) (.branch 28 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.leaf (-2)) (.leaf (0))),
  (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.leaf (-3)) (.leaf (-2))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-9)) (.leaf (-8))) (.branch 23 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-24)) (.branch 7 (.leaf (-23)) (.leaf (-22)))) (.branch 9 (.leaf (-21)) (.branch 10 (.leaf (-20)) (.leaf (-19))))) (.branch 14 (.branch 12 (.leaf (-18)) (.branch 13 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-13)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-12)) (.branch 19 (.leaf (-11)) (.leaf (-10)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD8_237_3244 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (7)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (1)) (.leaf (4)))))))
  code := certificateD8_3244
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 26 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-21))),
  (.branch 11 (.leaf (0)) (.leaf (-18))),
  (.branch 25 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 21 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-5)) (.leaf (-4)))),
  (.branch 18 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.branch 23 (.branch 8 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 20 (.branch 5 (.leaf (-21)) (.leaf (-20))) (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-16)) (.leaf (-14))))) (.branch 26 (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-8)))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 20 (.branch 15 (.branch 13 (.branch 12 (.leaf (-18)) (.leaf (-17))) (.branch 14 (.leaf (-16)) (.leaf (-15)))) (.branch 17 (.branch 16 (.leaf (-14)) (.leaf (-13))) (.branch 18 (.leaf (-12)) (.branch 19 (.leaf (-11)) (.leaf (-10)))))) (.branch 24 (.branch 22 (.branch 21 (.leaf (-9)) (.leaf (-8))) (.branch 23 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_237_3245 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (7)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (3)) (.leaf (2)))))))
  code := certificateD8_3245
  counts := ![(.branch 13 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 20 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 23 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 6 (.leaf (-11)) (.branch 9 (.leaf (-12)) (.leaf (-13))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 22 (.leaf (-11)) (.leaf (-12)))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (-4)) (.leaf (-6)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-25))),
  (.branch 18 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 27 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 28 (.leaf (-9)) (.leaf (-6)))),
  (.branch 23 (.leaf (-12)) (.branch 28 (.leaf (-10)) (.leaf (-7)))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-1)) (.leaf (0)))),
  (.branch 18 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2))))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 16 (.branch 10 (.branch 7 (.branch 5 (.leaf (-25)) (.branch 6 (.leaf (-24)) (.leaf (-23)))) (.branch 8 (.leaf (-22)) (.branch 9 (.leaf (-21)) (.leaf (-20))))) (.branch 13 (.branch 11 (.leaf (-19)) (.branch 12 (.leaf (-18)) (.leaf (-17)))) (.branch 14 (.leaf (-16)) (.branch 15 (.leaf (-15)) (.leaf (-14)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-13)) (.branch 18 (.leaf (-12)) (.leaf (-11)))) (.branch 20 (.leaf (-10)) (.branch 21 (.leaf (-9)) (.leaf (-8))))) (.branch 25 (.branch 23 (.leaf (-7)) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-11)) (.leaf (-10))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_237_3246 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (4)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (6)) (.leaf (2)))))))
  code := certificateD8_3246
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-11)) (.leaf (-17)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13))))]
  high := ![(.branch 16 (.branch 7 (.branch 4 (.leaf (-28)) (.leaf (-27))) (.branch 10 (.leaf (-26)) (.branch 13 (.leaf (-25)) (.leaf (-24))))) (.branch 22 (.branch 19 (.leaf (-23)) (.leaf (-22))) (.branch 25 (.leaf (-21)) (.branch 28 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 15 (.branch 3 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17)))) (.branch 27 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-15)) (.leaf (-13)))) (.branch 27 (.leaf (-11)) (.branch 28 (.leaf (-9)) (.leaf (-7))))),
  (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 23 (.branch 8 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 14 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_237_3247 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (7)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (3)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (6)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (7)) (.leaf (4)))))))
  code := certificateD8_3247
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-17)) (.leaf (-24)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.branch 24 (.leaf (-19)) (.leaf (-20))))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 14 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 14 (.branch 5 (.leaf (-24)) (.leaf (-23))) (.branch 23 (.leaf (-22)) (.branch 28 (.leaf (-19)) (.leaf (-14))))),
  (.branch 22 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-16))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-8)) (.leaf (-4))))),
  (.branch 26 (.branch 6 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 9 (.leaf (-13)) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-16))) (.branch 23 (.leaf (-14)) (.leaf (-12)))) (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (-2))]
def witnessD8_237_3248 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (7))) (.branch 24 (.leaf (2)) (.leaf (4)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (5)))))))
  code := certificateD8_3248
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-17)) (.leaf (-24)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.branch 24 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-21))),
  (.branch 23 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 14 (.branch 5 (.leaf (-24)) (.leaf (-23))) (.branch 23 (.leaf (-22)) (.branch 28 (.leaf (-19)) (.leaf (-14))))),
  (.branch 22 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-16))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-8)) (.leaf (-4))))),
  (.branch 21 (.leaf (-6)) (.leaf (-4))),
  (.branch 26 (.branch 6 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-21)) (.leaf (-20))) (.branch 11 (.leaf (-19)) (.branch 12 (.leaf (-18)) (.leaf (-17))))) (.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-14)) (.branch 17 (.leaf (-13)) (.leaf (-12)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-11)) (.leaf (-10))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_237_3249 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (7)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (5)))))))
  code := certificateD8_3249
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-14)) (.leaf (-17)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-24))),
  (.branch 18 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 13 (.branch 3 (.leaf (-17)) (.branch 8 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.branch 18 (.leaf (-14)) (.leaf (-13))) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.branch 21 (.branch 15 (.leaf (-17)) (.leaf (-16))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 9 (.leaf (-13)) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-24)) (.branch 7 (.leaf (-23)) (.leaf (-22)))) (.branch 9 (.leaf (-21)) (.branch 10 (.leaf (-20)) (.leaf (-19))))) (.branch 14 (.branch 12 (.leaf (-18)) (.branch 13 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-13)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-12)) (.branch 19 (.leaf (-11)) (.leaf (-10)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-11)) (.leaf (-10))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_237_3250 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (6)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (7))) (.branch 24 (.leaf (0)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (2)) (.leaf (3)))))))
  code := certificateD8_3250
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-24)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.leaf (-20))),
  (.branch 23 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 26 (.branch 19 (.leaf (-26)) (.branch 25 (.leaf (-25)) (.leaf (-20)))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 15 (.branch 3 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17)))) (.branch 27 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 20 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 28 (.leaf (-7)) (.leaf (-4)))),
  (.branch 26 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-20)) (.leaf (-19))) (.branch 12 (.leaf (-18)) (.branch 13 (.leaf (-17)) (.leaf (-16))))) (.branch 16 (.branch 15 (.leaf (-15)) (.leaf (-14))) (.branch 17 (.leaf (-13)) (.branch 18 (.leaf (-12)) (.leaf (-11)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-10)) (.leaf (-9))) (.branch 22 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-6))))) (.branch 26 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_237_3251 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (4))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (6)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (3))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (3)) (.leaf (7)))))))
  code := certificateD8_3251
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-24))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-21))) (.branch 16 (.leaf (-22)) (.branch 23 (.leaf (-23)) (.leaf (-24))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.branch 24 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 26 (.leaf (-8)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-13)) (.leaf (-20)))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 8 (.branch 2 (.leaf (-24)) (.leaf (-23))) (.branch 14 (.leaf (-22)) (.leaf (-21)))) (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 24 (.leaf (-24)) (.branch 25 (.leaf (-20)) (.leaf (-16)))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-8)) (.leaf (-4))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-16))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-8)) (.leaf (-4))))),
  (.branch 7 (.leaf (-5)) (.leaf (-4))),
  (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-7)) (.leaf (-4)))),
  (.branch 28 (.leaf (-6)) (.leaf (-3))),
  (.branch 25 (.branch 23 (.branch 12 (.leaf (-20)) (.leaf (-19))) (.branch 24 (.leaf (-17)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-13)) (.leaf (-11))) (.branch 28 (.leaf (-9)) (.leaf (-7))))),
  (.leaf (0))]
def witnessD8_237_3252 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (0)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (4))) (.branch 20 (.leaf (0)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (5)) (.leaf (3))) (.branch 24 (.leaf (2)) (.leaf (0)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (7))) (.branch 28 (.leaf (2)) (.leaf (4)))))))
  code := certificateD8_3252
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-10)))) (.branch 12 (.leaf (-11)) (.branch 20 (.leaf (-12)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-15))),
  (.branch 27 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 26 (.branch 21 (.leaf (-14)) (.leaf (-13))) (.branch 27 (.leaf (-11)) (.branch 28 (.leaf (-9)) (.leaf (-7))))),
  (.branch 22 (.branch 12 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-2)),
  (.branch 25 (.branch 14 (.branch 4 (.leaf (-20)) (.leaf (-19))) (.branch 24 (.leaf (-18)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 23 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.leaf (-2))))),
  (.branch 21 (.branch 17 (.branch 15 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-13)))) (.branch 19 (.branch 18 (.leaf (-12)) (.leaf (-11))) (.branch 20 (.leaf (-10)) (.leaf (-9))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-7))) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_237_3253 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (4))) (.branch 13 (.leaf (1)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (5)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (7)) (.leaf (2))) (.branch 24 (.leaf (3)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (4)) (.leaf (5)))))))
  code := certificateD8_3253
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-19)) (.leaf (-23)))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 16 (.leaf (-12)) (.leaf (-13)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-21))),
  (.branch 22 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 27 (.branch 22 (.leaf (-18)) (.leaf (-15))) (.branch 28 (.leaf (-11)) (.leaf (-7)))),
  (.branch 20 (.branch 8 (.leaf (-23)) (.branch 14 (.leaf (-22)) (.leaf (-21)))) (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 17 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-6)) (.leaf (-4))))),
  (.branch 13 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 18 (.branch 13 (.branch 10 (.branch 9 (.leaf (-21)) (.leaf (-20))) (.branch 11 (.leaf (-19)) (.branch 12 (.leaf (-18)) (.leaf (-17))))) (.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-14)) (.branch 17 (.leaf (-13)) (.leaf (-12)))))) (.branch 23 (.branch 20 (.branch 19 (.leaf (-11)) (.leaf (-10))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.leaf (-7)) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_237_3254 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (5))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (7)) (.leaf (2)))))))
  code := certificateD8_3254
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 24 (.leaf (-14)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-16)))),
  (.branch 13 (.leaf (0)) (.leaf (-16))),
  (.branch 28 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 24 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-4))))),
  (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5)))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 26 (.branch 25 (.leaf (-16)) (.leaf (-13))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-7)) (.leaf (-4))))),
  (.branch 17 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-16)) (.leaf (-14))) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-14)) (.leaf (-13)))) (.branch 19 (.branch 18 (.leaf (-12)) (.leaf (-11))) (.branch 20 (.leaf (-10)) (.leaf (-9))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-7))) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD8_237_3255 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (6))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (7)) (.branch 16 (.leaf (0)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (1)) (.leaf (6))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (7)))))))
  code := certificateD8_3255
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 19 (.leaf (-21)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 18 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-20)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-15)) (.leaf (-16)))),
  (.leaf (0))]
  high := ![(.branch 24 (.branch 20 (.leaf (-22)) (.leaf (-19))) (.branch 28 (.leaf (-16)) (.leaf (-8)))),
  (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5)))),
  (.branch 27 (.branch 19 (.leaf (-15)) (.leaf (-12))) (.branch 28 (.leaf (-8)) (.leaf (-4)))),
  (.branch 25 (.branch 23 (.leaf (-21)) (.branch 24 (.leaf (-18)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 7 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7)))),
  (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-16)) (.leaf (-14))) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD8_237_3256 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (3)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (7))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (2)))))))
  code := certificateD8_3256
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-21))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-19)) (.leaf (-23)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 10 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-23))),
  (.branch 21 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 13 (.branch 2 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.branch 28 (.leaf (-16)) (.leaf (-8))))),
  (.branch 20 (.branch 8 (.leaf (-23)) (.branch 14 (.leaf (-22)) (.leaf (-21)))) (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-7)) (.leaf (-4))))),
  (.branch 25 (.branch 5 (.leaf (-17)) (.branch 15 (.leaf (-16)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-8)) (.leaf (-7))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 7 (.leaf (-23)) (.leaf (-22))) (.branch 9 (.leaf (-21)) (.branch 10 (.leaf (-20)) (.leaf (-19))))) (.branch 14 (.branch 12 (.leaf (-18)) (.branch 13 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-13)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-12)) (.branch 19 (.leaf (-11)) (.leaf (-10)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-7))) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_237_3257 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (7)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (5)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (4)) (.leaf (2)))))))
  code := certificateD8_3257
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-19)) (.leaf (-22)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-4)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-25))),
  (.branch 17 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 17 (.branch 7 (.branch 2 (.leaf (-23)) (.leaf (-22))) (.branch 12 (.leaf (-21)) (.leaf (-20)))) (.branch 27 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.branch 26 (.branch 14 (.leaf (-22)) (.branch 20 (.leaf (-21)) (.leaf (-20)))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-4)),
  (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.branch 10 (.branch 7 (.branch 5 (.leaf (-25)) (.branch 6 (.leaf (-24)) (.leaf (-23)))) (.branch 8 (.leaf (-22)) (.branch 9 (.leaf (-21)) (.leaf (-20))))) (.branch 13 (.branch 11 (.leaf (-19)) (.branch 12 (.leaf (-18)) (.leaf (-17)))) (.branch 14 (.leaf (-16)) (.branch 15 (.leaf (-15)) (.leaf (-14)))))) (.branch 22 (.branch 19 (.branch 17 (.leaf (-13)) (.branch 18 (.leaf (-12)) (.leaf (-11)))) (.branch 20 (.leaf (-10)) (.branch 21 (.leaf (-9)) (.leaf (-8))))) (.branch 25 (.branch 23 (.leaf (-7)) (.branch 24 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 23 (.branch 20 (.branch 18 (.leaf (-12)) (.branch 19 (.leaf (-11)) (.leaf (-10)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_237_3258 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (7)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (6)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (4)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (7))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (5)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (2)) (.leaf (6)))))))
  code := certificateD8_3258
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 26 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-19)) (.leaf (-23)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (-9)) (.leaf (-10)))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-7)) (.leaf (-4)))),
  (.branch 20 (.branch 8 (.leaf (-23)) (.branch 14 (.leaf (-22)) (.leaf (-21)))) (.branch 27 (.branch 26 (.leaf (-20)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 20 (.branch 4 (.leaf (-23)) (.branch 19 (.leaf (-22)) (.leaf (-20)))) (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-16)) (.leaf (-14))))) (.branch 26 (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-8)))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 22 (.branch 7 (.leaf (-17)) (.leaf (-16))) (.branch 23 (.leaf (-14)) (.leaf (-12)))) (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))))]
def witnessD8_237_3259 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (7))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (6)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (4)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (7)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (4))) (.branch 24 (.leaf (6)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (5)) (.leaf (2)))))))
  code := certificateD8_3259
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-23))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-21)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-10)) (.leaf (-12))))]
  high := ![(.branch 17 (.branch 7 (.branch 2 (.leaf (-23)) (.leaf (-22))) (.branch 12 (.leaf (-21)) (.leaf (-20)))) (.branch 27 (.branch 22 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.branch 26 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 5 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-4)))),
  (.branch 25 (.branch 14 (.branch 4 (.leaf (-20)) (.leaf (-19))) (.branch 24 (.leaf (-18)) (.leaf (-15)))) (.branch 27 (.branch 26 (.leaf (-12)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-8)) (.leaf (-7))),
  (.branch 26 (.branch 10 (.leaf (-11)) (.branch 25 (.leaf (-10)) (.leaf (-8)))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_237_3260 : CycleWitness 8 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (6)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (7)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (3)))))))
  code := certificateD8_3260
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-25)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-23)) (.leaf (-24)))),
  (.branch 10 (.leaf (0)) (.leaf (-19))),
  (.branch 25 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-25)) (.leaf (-23))) (.branch 24 (.leaf (-21)) (.branch 28 (.leaf (-19)) (.leaf (-12))))),
  (.branch 22 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-16))) (.branch 23 (.leaf (-14)) (.leaf (-12)))) (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 23 (.branch 20 (.branch 18 (.leaf (-24)) (.branch 19 (.leaf (-22)) (.leaf (-20)))) (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-16)) (.leaf (-14))))) (.branch 26 (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-8)))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 19 (.branch 14 (.branch 12 (.branch 11 (.leaf (-19)) (.leaf (-18))) (.branch 13 (.leaf (-17)) (.leaf (-16)))) (.branch 16 (.branch 15 (.leaf (-15)) (.leaf (-14))) (.branch 17 (.leaf (-13)) (.branch 18 (.leaf (-12)) (.leaf (-11)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-10)) (.leaf (-9))) (.branch 22 (.leaf (-8)) (.branch 23 (.leaf (-7)) (.leaf (-6))))) (.branch 26 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 26 (.leaf (-4)) (.leaf (-3))) (.branch 28 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_237 : Fin 34 → CycleWitness 8 := ![witnessD8_237_3227, witnessD8_237_3228, witnessD8_237_3229, witnessD8_237_3230, witnessD8_237_3231, witnessD8_237_3232, witnessD8_237_3233, witnessD8_237_3234, witnessD8_237_3235, witnessD8_237_3236, witnessD8_237_3237, witnessD8_237_3238, witnessD8_237_3239, witnessD8_237_3240, witnessD8_237_3241, witnessD8_237_3242, witnessD8_237_3243, witnessD8_237_3244, witnessD8_237_3245, witnessD8_237_3246, witnessD8_237_3247, witnessD8_237_3248, witnessD8_237_3249, witnessD8_237_3250, witnessD8_237_3251, witnessD8_237_3252, witnessD8_237_3253, witnessD8_237_3254, witnessD8_237_3255, witnessD8_237_3256, witnessD8_237_3257, witnessD8_237_3258, witnessD8_237_3259, witnessD8_237_3260]
end RealPinwheel.FiveSixths


