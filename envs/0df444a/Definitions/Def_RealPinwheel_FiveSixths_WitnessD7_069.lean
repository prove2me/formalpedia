-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_069
-- name    : RealPinwheel_FiveSixths_WitnessD7_069
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:23:21.344055+00:00
-- url     : https://prove2.me/theorems/ad6b96f6-c54d-445d-a202-698abf68326f
-- title:
--   Exact witness block D7_069
-- statement:
--   These exact witnesses represent words 1434 through 1482 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1434–1482; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_069_1433 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (6)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1433
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-10)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-1)) (.leaf (-3)))),
  (.branch 14 (.leaf (0)) (.branch 20 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 19 (.leaf (-10)) (.branch 20 (.leaf (-7)) (.leaf (-4))))),
  (.branch 16 (.leaf (-3)) (.leaf (0))),
  (.leaf (-4)),
  (.branch 12 (.branch 7 (.branch 5 (.branch 4 (.leaf (-18)) (.leaf (-17))) (.branch 6 (.leaf (-16)) (.leaf (-15)))) (.branch 9 (.branch 8 (.leaf (-14)) (.leaf (-13))) (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-11)) (.leaf (-10)))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-7)) (.leaf (-6)))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-11)) (.leaf (-10)))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_069_1434 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1434
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 16 (.leaf (-6)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (0)),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-11)) (.leaf (-10)))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_069_1435 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1435
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.branch 5 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-13)) (.branch 20 (.leaf (-9)) (.leaf (-5))))),
  (.branch 7 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-13)) (.branch 10 (.leaf (-12)) (.leaf (-11)))) (.branch 12 (.leaf (-10)) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_069_1436 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1436
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 17 (.leaf (-15)) (.leaf (-17))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-13))) (.branch 20 (.leaf (-9)) (.leaf (-5)))),
  (.branch 19 (.branch 13 (.leaf (-15)) (.leaf (-12))) (.branch 20 (.leaf (-8)) (.leaf (-4)))),
  (.branch 17 (.branch 16 (.leaf (-3)) (.leaf (-2))) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-13)) (.branch 10 (.leaf (-12)) (.leaf (-11)))) (.branch 12 (.leaf (-10)) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_069_1437 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (5)) (.leaf (2)))))))
  code := certificateD7_1437
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))) (.branch 13 (.leaf (-18)) (.branch 17 (.leaf (-19)) (.leaf (-20))))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-4)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-15))) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 13 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 7 (.leaf (-7)) (.leaf (-6))),
  (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1438 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (2)))))))
  code := certificateD7_1438
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 9 (.leaf (-1)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-15)) (.leaf (-16)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 16 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 15 (.branch 2 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.leaf (-5)))),
  (.branch 19 (.branch 13 (.leaf (-15)) (.leaf (-12))) (.branch 20 (.leaf (-8)) (.leaf (-4)))),
  (.branch 16 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-14))) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1439 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (6))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1439
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))) (.branch 13 (.leaf (-18)) (.branch 17 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 14 (.leaf (-10)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 19 (.branch 18 (.leaf (-20)) (.leaf (-15))) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 15 (.leaf (-12)) (.branch 20 (.leaf (-9)) (.leaf (-5)))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 17 (.branch 4 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-14)) (.branch 9 (.leaf (-13)) (.leaf (-12)))) (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_069_1440 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_1440
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 12 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 19 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 20 (.leaf (-6)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-17)) (.leaf (-16))) (.branch 7 (.leaf (-15)) (.leaf (-14)))) (.branch 10 (.branch 9 (.leaf (-13)) (.leaf (-12))) (.branch 11 (.leaf (-11)) (.leaf (-10))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-7)) (.leaf (-6)))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-10)) (.leaf (-9))) (.branch 14 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-6))))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_069_1441 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1441
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.leaf (-18)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-10)) (.leaf (-14)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 13 (.leaf (-6)) (.leaf (-7)))),
  (.branch 15 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 19 (.branch 10 (.leaf (-18)) (.leaf (-15))) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 12 (.leaf (-8)) (.leaf (-5))),
  (.branch 18 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 19 (.leaf (-10)) (.branch 20 (.leaf (-7)) (.leaf (-4))))),
  (.branch 14 (.leaf (-7)) (.branch 20 (.leaf (-6)) (.leaf (-4)))),
  (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_069_1442 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (5)))))))
  code := certificateD7_1442
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-16)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 19 (.branch 6 (.leaf (-17)) (.leaf (-15))) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 8 (.leaf (-7)) (.leaf (-5))),
  (.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-7)) (.leaf (-4)))),
  (.branch 18 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 17 (.branch 5 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.leaf (-2)) (.branch 11 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-10)) (.leaf (-9))) (.branch 14 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-6))))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_069_1443 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_1443
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 9 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.branch 14 (.leaf (-19)) (.leaf (-15))) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 13 (.leaf (-3)) (.leaf (0))),
  (.branch 15 (.leaf (-10)) (.branch 20 (.leaf (-8)) (.leaf (-5)))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-15)) (.branch 8 (.leaf (-14)) (.leaf (-13)))) (.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 12 (.leaf (-10)) (.leaf (-9))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1444 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_1444
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 15 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 15 (.branch 2 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.leaf (-5)))),
  (.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-8)) (.leaf (-4)))),
  (.branch 12 (.leaf (-5)) (.leaf (-4))),
  (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-16)) (.leaf (-15))) (.branch 8 (.leaf (-14)) (.leaf (-13)))) (.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 12 (.leaf (-10)) (.leaf (-9))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1445 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (6)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (4)) (.branch 20 (.leaf (1)) (.leaf (5)))))))
  code := certificateD7_1445
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 11 (.leaf (-18)) (.leaf (-19)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-3)) (.leaf (-4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 18 (.branch 12 (.leaf (-19)) (.leaf (-16))) (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-4)),
  (.branch 19 (.branch 13 (.leaf (-15)) (.leaf (-12))) (.branch 20 (.leaf (-8)) (.leaf (-4)))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.leaf (-5)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-13)) (.branch 10 (.leaf (-12)) (.leaf (-11)))) (.branch 12 (.leaf (-10)) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_069_1446 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (6))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1446
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 11 (.leaf (5)) (.branch 12 (.leaf (6)) (.leaf (7)))) (.branch 16 (.leaf (8)) (.branch 19 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_069_1447 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (2))) (.branch 9 (.leaf (0)) (.leaf (4))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (5)))) (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1447
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 14 (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 17 (.branch 16 (.leaf (9)) (.leaf (10))) (.branch 19 (.leaf (11)) (.leaf (12)))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 18 (.leaf (-4)) (.leaf (-3))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_069_1448 : CycleWitness 7 where
  length := 20
  word := (.branch 11 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 17 (.branch 16 (.leaf (6)) (.leaf (0))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1448
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 17 (.leaf (9)) (.branch 19 (.leaf (10)) (.leaf (11)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 9 (.leaf (-10)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 14 (.branch 10 (.leaf (-12)) (.branch 12 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))),
  (.branch 19 (.leaf (-6)) (.leaf (-3))),
  (.branch 16 (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_069_1449 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (5)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (0))) (.branch 17 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1449
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 18 (.leaf (9)) (.branch 19 (.leaf (10)) (.leaf (11)))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 3 (.leaf (-14)) (.leaf (-13))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1450 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1450
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 11 (.leaf (5)) (.branch 12 (.leaf (6)) (.leaf (7)))) (.branch 16 (.leaf (8)) (.branch 19 (.leaf (9)) (.leaf (10)))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_069_1451 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1451
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 4 (.leaf (-18)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 18 (.leaf (-4)) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 6 (.leaf (-15)) (.leaf (-14)))) (.branch 9 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.leaf (-10))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_069_1452 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (1)))))))
  code := certificateD7_1452
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 11 (.leaf (5)) (.branch 13 (.leaf (6)) (.leaf (7)))) (.branch 17 (.leaf (8)) (.branch 18 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_069_1453 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1453
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 14 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 16 (.leaf (7)) (.branch 18 (.leaf (8)) (.leaf (9)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 4 (.leaf (-18)) (.leaf (-20)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 12 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-11)))),
  (.branch 18 (.leaf (-4)) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 6 (.leaf (-15)) (.leaf (-14)))) (.branch 9 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.leaf (-10))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1454 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1454
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 16 (.branch 8 (.leaf (-17)) (.leaf (-16))) (.branch 19 (.leaf (-14)) (.leaf (-9)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 18 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 6 (.leaf (-15)) (.leaf (-14)))) (.branch 9 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.leaf (-10))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1455 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1455
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1456 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1456
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 19 (.leaf (-4)) (.leaf (-2))),
  (.branch 16 (.leaf (-5)) (.leaf (-3))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_069_1457 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1457
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-6)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 14 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_069_1458 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1458
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 11 (.leaf (0)) (.leaf (-9))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_069_1459 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1459
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 19 (.leaf (-4)) (.leaf (-2))),
  (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 6 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1460 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (3)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1460
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 11 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_069_1461 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1461
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-10)))),
  (.leaf (0))]
  high := ![(.branch 19 (.leaf (-4)) (.leaf (-2))),
  (.branch 17 (.branch 16 (.leaf (-15)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-8)) (.leaf (-7)))) (.branch 18 (.branch 17 (.leaf (-6)) (.leaf (-5))) (.branch 19 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD7_069_1462 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1462
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-13)))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 4 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-7))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))))),
  (.leaf (0))]
def witnessD7_069_1463 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (5))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1463
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 17 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 6 (.leaf (-5)) (.branch 19 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_069_1464 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1464
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 8 (.leaf (-5)) (.branch 11 (.leaf (-6)) (.leaf (-7))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 8 (.branch 2 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 14 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-7))))),
  (.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_069_1465 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (0))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1465
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.leaf (-5)) (.leaf (-3))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_069_1466 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (6)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1466
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_069_1467 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (5)))))))
  code := certificateD7_1467
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 15 (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_069_1468 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (5))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1468
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 8 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_069_1469 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1469
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_069_1470 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (3)) (.branch 19 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1470
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.leaf (-4)) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_069_1471 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1471
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_069_1472 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1472
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1473 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1473
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 19 (.leaf (-14)) (.leaf (-7))),
  (.branch 17 (.branch 9 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-4)) (.branch 19 (.leaf (-3)) (.leaf (-2)))),
  (.branch 13 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_069_1474 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (1)) (.leaf (6))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1474
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1475 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1475
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 3 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1476 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (6))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (5)))))))
  code := certificateD7_1476
  counts := ![(.branch 10 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 19 (.leaf (-3)) (.leaf (-2))),
  (.branch 17 (.branch 9 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 18 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_069_1477 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (5)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (4)) (.leaf (3))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1477
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_069_1478 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (5))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (0))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1478
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 8 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 5 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1479 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (6)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1479
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-13)))),
  (.branch 6 (.leaf (0)) (.branch 19 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_069_1480 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (4))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (5))) (.branch 18 (.leaf (1)) (.branch 19 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1480
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-12)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 7 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-2)),
  (.branch 18 (.leaf (-5)) (.branch 19 (.leaf (-4)) (.leaf (-3)))),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_069_1481 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1481
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 16 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 19 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_069 : Fin 49 → CycleWitness 7 := ![witnessD7_069_1433, witnessD7_069_1434, witnessD7_069_1435, witnessD7_069_1436, witnessD7_069_1437, witnessD7_069_1438, witnessD7_069_1439, witnessD7_069_1440, witnessD7_069_1441, witnessD7_069_1442, witnessD7_069_1443, witnessD7_069_1444, witnessD7_069_1445, witnessD7_069_1446, witnessD7_069_1447, witnessD7_069_1448, witnessD7_069_1449, witnessD7_069_1450, witnessD7_069_1451, witnessD7_069_1452, witnessD7_069_1453, witnessD7_069_1454, witnessD7_069_1455, witnessD7_069_1456, witnessD7_069_1457, witnessD7_069_1458, witnessD7_069_1459, witnessD7_069_1460, witnessD7_069_1461, witnessD7_069_1462, witnessD7_069_1463, witnessD7_069_1464, witnessD7_069_1465, witnessD7_069_1466, witnessD7_069_1467, witnessD7_069_1468, witnessD7_069_1469, witnessD7_069_1470, witnessD7_069_1471, witnessD7_069_1472, witnessD7_069_1473, witnessD7_069_1474, witnessD7_069_1475, witnessD7_069_1476, witnessD7_069_1477, witnessD7_069_1478, witnessD7_069_1479, witnessD7_069_1480, witnessD7_069_1481]
end RealPinwheel.FiveSixths


