-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_066
-- name    : RealPinwheel_FiveSixths_WitnessD7_066
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:20:17.982924+00:00
-- url     : https://prove2.me/theorems/a895a2df-143c-4284-a3c6-114ea166c203
-- title:
--   Exact witness block D7_066
-- statement:
--   These exact witnesses represent words 1306 through 1345 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1306–1345; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_066_1305 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (5)) (.branch 15 (.leaf (0)) (.leaf (1)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (6)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (4)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (1)) (.leaf (5)))))))
  code := certificateD7_1305
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 15 (.leaf (-16)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-10))))]
  high := ![(.branch 20 (.branch 16 (.leaf (-20)) (.leaf (-19))) (.branch 24 (.leaf (-18)) (.branch 25 (.leaf (-13)) (.leaf (-8))))),
  (.branch 7 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-5))))),
  (.branch 23 (.branch 5 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-7)))) (.branch 24 (.branch 23 (.leaf (-6)) (.leaf (-5))) (.branch 25 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_066_1306 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (6)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (3)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (2))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1306
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 23 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 13 (.leaf (-12)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-4)))),
  (.branch 14 (.leaf (-13)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-9)) (.leaf (-8))) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1307 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (6)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1307
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 17 (.leaf (-16)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 18 (.leaf (-19)) (.branch 25 (.leaf (-16)) (.leaf (-9)))),
  (.branch 3 (.leaf (-9)) (.leaf (-8))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1308 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (5)))))))
  code := certificateD7_1308
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 11 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 25 (.leaf (-10)) (.leaf (-5))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3)))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1309 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (2)))))))
  code := certificateD7_1309
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 25 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-4))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 18 (.leaf (-10)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.branch 8 (.leaf (-17)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.leaf (-4)) (.leaf (0))),
  (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 19 (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1310 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1310
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-16))) (.branch 12 (.leaf (-17)) (.branch 17 (.leaf (-18)) (.leaf (-19))))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.branch 18 (.leaf (-19)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 5 (.leaf (-6)) (.leaf (-5))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_066_1311 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (2)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1311
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 23 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 18 (.leaf (-10)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-4)))),
  (.branch 23 (.branch 14 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_066_1312 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (5))) (.branch 12 (.leaf (4)) (.leaf (1)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (5))) (.branch 25 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1312
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-4))))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 23 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-8)) (.branch 25 (.leaf (-6)) (.leaf (-4))))),
  (.branch 24 (.branch 8 (.leaf (-17)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.leaf (-4)) (.leaf (0))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 22 (.branch 4 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_066_1313 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1313
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-15))),
  (.branch 24 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-11)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.leaf (-7)) (.leaf (-5))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 24 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3))))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))) (.branch 16 (.branch 15 (.leaf (-12)) (.leaf (-11))) (.branch 17 (.leaf (-10)) (.leaf (-9))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_066_1314 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (5)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (5)))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (6)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1314
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-11)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.branch 4 (.leaf (-17)) (.branch 13 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_066_1315 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1315
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-11)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.leaf (-7)) (.leaf (-5))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.branch 12 (.leaf (-7)) (.branch 22 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.leaf (-4)) (.branch 25 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_066_1316 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (6)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1316
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-23))),
  (.branch 16 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 18 (.leaf (-10)) (.branch 25 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 8 (.branch 5 (.branch 4 (.leaf (-23)) (.leaf (-22))) (.branch 6 (.leaf (-21)) (.branch 7 (.leaf (-20)) (.leaf (-19))))) (.branch 11 (.branch 9 (.leaf (-18)) (.branch 10 (.leaf (-17)) (.leaf (-16)))) (.branch 12 (.leaf (-15)) (.branch 13 (.leaf (-14)) (.leaf (-13)))))) (.branch 20 (.branch 17 (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-11)) (.leaf (-10)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7))))) (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1317 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (6)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (3)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (6)))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1317
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 17 (.leaf (-18)) (.branch 22 (.leaf (-19)) (.leaf (-20))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-11)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-15))) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.leaf (-7)) (.leaf (-5))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))) (.branch 23 (.branch 22 (.leaf (-5)) (.leaf (-4))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1318 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (4)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (4))))) (.branch 22 (.branch 20 (.leaf (1)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1318
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 13 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.leaf (-6)) (.leaf (-3))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-13)) (.branch 15 (.leaf (-12)) (.leaf (-11)))) (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8))))) (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_066_1319 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (0)))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1319
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.branch 16 (.leaf (-23)) (.leaf (-24))))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 23 (.branch 17 (.leaf (-24)) (.leaf (-20))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-10)) (.leaf (-5))))),
  (.branch 4 (.leaf (-11)) (.branch 25 (.leaf (-10)) (.leaf (-5)))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-5)) (.leaf (-4)))) (.branch 24 (.leaf (-3)) (.branch 25 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_066_1320 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (1)))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (5)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1320
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 22 (.leaf (-7)) (.leaf (-5)))),
  (.branch 24 (.branch 17 (.leaf (-7)) (.leaf (-6))) (.branch 25 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 12 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-15)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-9))) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 23 (.branch 5 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5)))) (.branch 24 (.branch 23 (.leaf (-4)) (.leaf (-3))) (.branch 25 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_066_1321 : CycleWitness 7 where
  length := 26
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (6)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (4)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))) (.branch 22 (.branch 20 (.leaf (5)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1321
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-21))) (.branch 11 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-6)) (.leaf (-7)))) (.branch 19 (.leaf (-8)) (.branch 24 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0))]
  high := ![(.branch 23 (.branch 12 (.leaf (-23)) (.leaf (-20))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-10)) (.leaf (-5))))),
  (.branch 25 (.leaf (-10)) (.leaf (-5))),
  (.branch 23 (.branch 22 (.leaf (-10)) (.leaf (-8))) (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-5)) (.branch 25 (.leaf (-4)) (.leaf (-3)))),
  (.branch 8 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-15)) (.leaf (-12)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD7_066_1322 : CycleWitness 7 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (4)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1322
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 19 (.branch 14 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (7)))) (.branch 22 (.leaf (8)) (.branch 24 (.leaf (9)) (.leaf (10)))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-10))),
  (.branch 20 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 24 (.leaf (-4)) (.leaf (-2))),
  (.leaf (-2)),
  (.branch 15 (.branch 10 (.branch 7 (.branch 6 (.leaf (-20)) (.leaf (-19))) (.branch 8 (.leaf (-18)) (.branch 9 (.leaf (-17)) (.leaf (-16))))) (.branch 12 (.branch 11 (.leaf (-15)) (.leaf (-14))) (.branch 13 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-11)))))) (.branch 20 (.branch 17 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 19 (.leaf (-7)) (.leaf (-6))))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 17 (.branch 13 (.branch 11 (.leaf (-15)) (.branch 12 (.leaf (-14)) (.leaf (-13)))) (.branch 15 (.branch 14 (.leaf (-12)) (.leaf (-11))) (.branch 16 (.leaf (-10)) (.leaf (-9))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-7))) (.branch 20 (.leaf (-6)) (.leaf (-5)))) (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 17 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 19 (.leaf (-7)) (.leaf (-6))))) (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_066_1323 : CycleWitness 7 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (1)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1323
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (5)) (.leaf (6))) (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 11 (.leaf (-17)) (.leaf (-21)))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-15)) (.leaf (-16)))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 14 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 19 (.branch 2 (.leaf (-9)) (.leaf (-8))) (.branch 22 (.leaf (-7)) (.leaf (-6)))),
  (.branch 16 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 20 (.leaf (-19)) (.branch 24 (.leaf (-18)) (.leaf (-13))))),
  (.branch 22 (.branch 4 (.leaf (-16)) (.branch 21 (.leaf (-15)) (.leaf (-12)))) (.branch 23 (.leaf (-9)) (.branch 24 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.branch 19 (.branch 18 (.leaf (-16)) (.leaf (-14))) (.branch 20 (.leaf (-12)) (.leaf (-10)))) (.branch 23 (.branch 22 (.leaf (-8)) (.leaf (-6))) (.branch 24 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 10 (.leaf (-7)) (.leaf (-6))) (.branch 24 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 16 (.branch 15 (.leaf (-11)) (.leaf (-10))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))) (.branch 22 (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_066_1324 : CycleWitness 7 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1324
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 22 (.leaf (-14)) (.leaf (-16)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 14 (.leaf (-15)) (.branch 18 (.leaf (-16)) (.leaf (-17))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-9)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 23 (.leaf (-16)) (.branch 24 (.leaf (-11)) (.leaf (-6)))),
  (.branch 19 (.leaf (-17)) (.branch 24 (.leaf (-12)) (.leaf (-6)))),
  (.branch 23 (.branch 22 (.leaf (-16)) (.leaf (-12))) (.branch 24 (.leaf (-8)) (.leaf (-4)))),
  (.branch 22 (.branch 12 (.leaf (-12)) (.branch 21 (.leaf (-11)) (.leaf (-9)))) (.branch 23 (.leaf (-7)) (.branch 24 (.leaf (-5)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-12)) (.branch 15 (.leaf (-11)) (.leaf (-10)))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))) (.branch 22 (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-5)) (.leaf (-4)))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_066_1325 : CycleWitness 7 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (5)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1325
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 15 (.leaf (-14)) (.branch 21 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 23 (.branch 14 (.leaf (-19)) (.leaf (-16))) (.branch 24 (.leaf (-11)) (.leaf (-6)))),
  (.branch 20 (.leaf (-8)) (.leaf (-6))),
  (.branch 23 (.branch 22 (.leaf (-16)) (.leaf (-12))) (.branch 24 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.leaf (-8)) (.branch 24 (.leaf (-6)) (.leaf (-3)))),
  (.branch 20 (.branch 18 (.branch 5 (.leaf (-17)) (.leaf (-16))) (.branch 19 (.leaf (-14)) (.leaf (-12)))) (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-8))) (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-8))) (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.leaf (-1)) (.leaf (0)))]
def witnessD7_066_1326 : CycleWitness 7 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (5)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (3)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1326
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-13)) (.leaf (-14)))) (.branch 18 (.branch 14 (.leaf (-15)) (.leaf (-16))) (.branch 22 (.leaf (-17)) (.leaf (-18))))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-19)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-11)) (.leaf (-12)))),
  (.branch 11 (.leaf (0)) (.leaf (-14))),
  (.branch 24 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 13 (.branch 2 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-6)))),
  (.branch 23 (.leaf (-18)) (.branch 24 (.leaf (-12)) (.leaf (-6)))),
  (.branch 9 (.leaf (-2)) (.leaf (0))),
  (.branch 20 (.branch 17 (.branch 16 (.leaf (-20)) (.leaf (-18))) (.branch 18 (.leaf (-16)) (.branch 19 (.leaf (-14)) (.leaf (-12))))) (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-8))) (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 22 (.branch 20 (.leaf (-12)) (.branch 21 (.leaf (-10)) (.leaf (-8)))) (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.branch 14 (.branch 12 (.leaf (-14)) (.branch 13 (.leaf (-13)) (.leaf (-12)))) (.branch 16 (.branch 15 (.leaf (-11)) (.leaf (-10))) (.branch 17 (.leaf (-9)) (.leaf (-8))))) (.branch 21 (.branch 19 (.leaf (-7)) (.branch 20 (.leaf (-6)) (.leaf (-5)))) (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_066_1327 : CycleWitness 7 where
  length := 25
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (4)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1327
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 8 (.branch 1 (.leaf (0)) (.leaf (-18))) (.branch 15 (.leaf (-19)) (.branch 22 (.leaf (-20)) (.leaf (-21))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 16 (.leaf (-10)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-15)))),
  (.branch 20 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 23 (.leaf (-21)) (.branch 24 (.leaf (-14)) (.leaf (-7)))),
  (.branch 23 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 24 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-11)) (.branch 24 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 15 (.leaf (-4)) (.leaf (-3))),
  (.branch 19 (.branch 16 (.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-11)) (.leaf (-10))))) (.branch 22 (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-7)))) (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.branch 24 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_066_1328 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (5))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 23 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1328
  counts := ![(.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 16 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 22 (.leaf (14)) (.branch 23 (.leaf (15)) (.leaf (16))))))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.leaf (-2)),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_066_1329 : CycleWitness 7 where
  length := 24
  word := (.branch 13 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (5)) (.leaf (0)))) (.branch 21 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1329
  counts := ![(.branch 12 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 21 (.branch 20 (.leaf (12)) (.leaf (13))) (.branch 23 (.leaf (14)) (.leaf (15)))))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 22 (.leaf (-7)) (.leaf (-5))),
  (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 7 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_066_1330 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 19 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 20 (.leaf (6)) (.leaf (0))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1330
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.leaf (10)))) (.branch 21 (.branch 19 (.leaf (11)) (.leaf (12))) (.branch 23 (.leaf (13)) (.leaf (14)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.leaf (-11)) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 16 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_066_1331 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (6)) (.branch 23 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1331
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 18 (.branch 14 (.branch 13 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.leaf (10)))) (.branch 21 (.branch 20 (.leaf (11)) (.leaf (12))) (.branch 23 (.leaf (13)) (.leaf (14)))))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-14))),
  (.branch 22 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 17 (.branch 13 (.branch 11 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 15 (.branch 14 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.leaf (-8))))) (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_066_1332 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1332
  counts := ![(.branch 10 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 16 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 15 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 14 (.branch 9 (.branch 6 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 7 (.leaf (-18)) (.branch 8 (.leaf (-17)) (.leaf (-16))))) (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_066_1333 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (6)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1333
  counts := ![(.branch 11 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 17 (.branch 3 (.leaf (-14)) (.leaf (-13))) (.branch 20 (.leaf (-12)) (.branch 23 (.leaf (-11)) (.leaf (-7))))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_066_1334 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1334
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_066_1335 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1335
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 21 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 23 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_066_1336 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1336
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 19 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 17 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-3)))) (.branch 20 (.leaf (-2)) (.branch 21 (.leaf (-1)) (.leaf (0))))),
  (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-17)) (.leaf (-16))) (.branch 10 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-10))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_066_1337 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1337
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 13 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 5 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-9)))),
  (.branch 14 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 11 (.branch 6 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-14)) (.branch 21 (.leaf (-13)) (.leaf (-9))))),
  (.branch 17 (.branch 7 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7)))) (.branch 22 (.branch 21 (.leaf (-6)) (.leaf (-5))) (.branch 23 (.leaf (-4)) (.leaf (-3))))),
  (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_066_1338 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1338
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 21 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 23 (.leaf (11)) (.leaf (12)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_066_1339 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (4)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1339
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 19 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0))))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1340 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (3)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1340
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 20 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-17)) (.leaf (-16))) (.branch 10 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-10))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_066_1341 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (4)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (6)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1341
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 17 (.branch 14 (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))) (.branch 15 (.leaf (-10)) (.branch 16 (.leaf (-9)) (.leaf (-8))))) (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1342 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (6)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1342
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 15 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 9 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.branch 19 (.leaf (-10)) (.leaf (-9))))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 9 (.branch 7 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 8 (.leaf (-17)) (.leaf (-16)))) (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1343 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1343
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 21 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 13 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 20 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 9 (.branch 7 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 8 (.leaf (-17)) (.leaf (-16)))) (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 18 (.branch 15 (.branch 14 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_066_1344 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1344
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 13 (.leaf (5)) (.branch 15 (.leaf (6)) (.leaf (7)))) (.branch 20 (.leaf (8)) (.branch 22 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_066 : Fin 40 → CycleWitness 7 := ![witnessD7_066_1305, witnessD7_066_1306, witnessD7_066_1307, witnessD7_066_1308, witnessD7_066_1309, witnessD7_066_1310, witnessD7_066_1311, witnessD7_066_1312, witnessD7_066_1313, witnessD7_066_1314, witnessD7_066_1315, witnessD7_066_1316, witnessD7_066_1317, witnessD7_066_1318, witnessD7_066_1319, witnessD7_066_1320, witnessD7_066_1321, witnessD7_066_1322, witnessD7_066_1323, witnessD7_066_1324, witnessD7_066_1325, witnessD7_066_1326, witnessD7_066_1327, witnessD7_066_1328, witnessD7_066_1329, witnessD7_066_1330, witnessD7_066_1331, witnessD7_066_1332, witnessD7_066_1333, witnessD7_066_1334, witnessD7_066_1335, witnessD7_066_1336, witnessD7_066_1337, witnessD7_066_1338, witnessD7_066_1339, witnessD7_066_1340, witnessD7_066_1341, witnessD7_066_1342, witnessD7_066_1343, witnessD7_066_1344]
end RealPinwheel.FiveSixths


