-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_068
-- name    : RealPinwheel_FiveSixths_WitnessD7_068
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:20:35.298933+00:00
-- url     : https://prove2.me/theorems/bbf3b81f-3f03-4390-9c1c-8bf0e5ac920f
-- title:
--   Exact witness block D7_068
-- statement:
--   These exact witnesses represent words 1388 through 1433 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1388–1433; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_068_1387 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (6))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1387
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 18 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-5)) (.leaf (-3)))),
  (.branch 9 (.leaf (-2)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.branch 13 (.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-11)) (.leaf (-10)))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 11 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-11)) (.leaf (-10))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1388 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1388
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 18 (.leaf (8)) (.branch 21 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.branch 7 (.leaf (-8)) (.leaf (-9))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 20 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 19 (.leaf (-9)) (.leaf (-5))),
  (.branch 19 (.branch 10 (.leaf (-17)) (.branch 18 (.leaf (-15)) (.leaf (-12)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 21 (.leaf (-6)) (.leaf (-3))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_068_1389 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (6)) (.branch 21 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1389
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 19 (.leaf (8)) (.branch 21 (.leaf (9)) (.leaf (10)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 17 (.leaf (-8)) (.leaf (-5))),
  (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-13)) (.branch 11 (.leaf (-12)) (.leaf (-11)))) (.branch 13 (.leaf (-10)) (.branch 14 (.leaf (-9)) (.leaf (-8))))) (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_068_1390 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (6))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1390
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-15)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 20 (.branch 4 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-13)) (.leaf (-7)))),
  (.branch 19 (.branch 13 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-11)) (.branch 21 (.leaf (-8)) (.leaf (-5))))),
  (.branch 7 (.leaf (-4)) (.leaf (-3))),
  (.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.branch 6 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1391 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (5)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (6)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (5)) (.leaf (4)))))))
  code := certificateD7_1391
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-15)) (.leaf (-16)))) (.branch 13 (.branch 10 (.leaf (-17)) (.leaf (-18))) (.branch 16 (.leaf (-19)) (.leaf (-20))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 9 (.leaf (-13)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 17 (.leaf (-20)) (.branch 21 (.leaf (-14)) (.leaf (-7)))),
  (.branch 15 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-10)) (.leaf (-7))))),
  (.branch 20 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 9 (.leaf (-4)) (.leaf (-3))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1392 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1392
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-18)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.leaf (-21))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-14)) (.leaf (-7)))),
  (.branch 9 (.leaf (-10)) (.leaf (-7))),
  (.branch 15 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1393 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (0)) (.leaf (2)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1393
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 13 (.leaf (-7)) (.leaf (-6))) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 17 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1394 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (3)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (1)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1394
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 20 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-3)))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-15)) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_068_1395 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (1)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1395
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 18 (.leaf (7)) (.branch 21 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-13))) (.branch 17 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 15 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 19 (.leaf (-14)) (.leaf (-9))),
  (.branch 20 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-8)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-15)) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_068_1396 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (1)) (.leaf (3)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1396
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 10 (.leaf (-15)) (.branch 16 (.leaf (-16)) (.leaf (-18))))),
  (.branch 2 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-7))) (.branch 19 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 17 (.leaf (-18)) (.branch 21 (.leaf (-13)) (.leaf (-7)))),
  (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))),
  (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1397 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (5)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (6)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1397
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 21 (.leaf (-8)) (.leaf (-4))),
  (.branch 14 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-3)))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 11 (.branch 9 (.leaf (-14)) (.branch 10 (.leaf (-13)) (.leaf (-12)))) (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.leaf (-8))))) (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_068_1398 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (5)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1398
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-15)) (.leaf (-16)))) (.branch 10 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-4)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-10)))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 14 (.leaf (-19)) (.branch 21 (.leaf (-14)) (.leaf (-7)))),
  (.branch 20 (.branch 13 (.leaf (-6)) (.leaf (-5))) (.branch 21 (.leaf (-4)) (.leaf (-3)))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 7 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (0)))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 17 (.leaf (-10)) (.branch 18 (.leaf (-9)) (.leaf (-8)))) (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-5))))),
  (.leaf (-1))]
def witnessD7_068_1399 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (3)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (6))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1399
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 18 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 11 (.leaf (-14)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.leaf (0)),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 11 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-11)) (.leaf (-10))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1400 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1400
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-15)) (.leaf (-16)))) (.branch 10 (.leaf (-17)) (.branch 13 (.leaf (-18)) (.leaf (-19))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 14 (.leaf (-19)) (.branch 21 (.leaf (-14)) (.leaf (-7)))),
  (.branch 12 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-7)))),
  (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6))))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 11 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-11)) (.leaf (-10))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_068_1401 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (6)) (.leaf (0))) (.branch 14 (.leaf (4)) (.branch 15 (.leaf (1)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1401
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-12)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-9))))),
  (.branch 16 (.leaf (-13)) (.branch 21 (.leaf (-10)) (.leaf (-5)))),
  (.branch 19 (.branch 11 (.leaf (-14)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_068_1402 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (4)) (.branch 7 (.leaf (3)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (6)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (5)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1402
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 17 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 20 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.leaf (0))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_068_1403 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1403
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (-15))) (.branch 7 (.leaf (-16)) (.leaf (-17)))) (.branch 16 (.branch 13 (.leaf (-18)) (.leaf (-19))) (.branch 19 (.leaf (-20)) (.leaf (-21))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-21)) (.branch 21 (.leaf (-14)) (.leaf (-7)))),
  (.branch 9 (.leaf (-10)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1404 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (6)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (5))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1404
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 21 (.leaf (-8)) (.leaf (-4))),
  (.branch 19 (.branch 3 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-12)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-5)) (.leaf (-3))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_068_1405 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (2)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (3)) (.branch 15 (.leaf (0)) (.leaf (6))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1405
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 15 (.leaf (-5)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 11 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-11)) (.leaf (-10))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1406 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (4)) (.leaf (0)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (1)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (4)) (.branch 15 (.leaf (0)) (.leaf (6))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (5)) (.branch 21 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1406
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 19 (.branch 3 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-12)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-5)) (.leaf (-3))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.leaf (0))),
  (.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1407 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (4)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (1)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1407
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-12)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-9))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 21 (.leaf (-10)) (.leaf (-5)))),
  (.branch 18 (.leaf (-2)) (.leaf (0))),
  (.branch 19 (.branch 11 (.leaf (-14)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-15)) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_068_1408 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (4)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (4)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (3)) (.leaf (1)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1408
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-8))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 17 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 20 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.leaf (-3)) (.leaf (-2))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.leaf (0))),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1409 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (6)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (4)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1409
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-12)) (.leaf (-13)))),
  (.branch 16 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-18))),
  (.branch 14 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-9))))),
  (.branch 16 (.leaf (-13)) (.branch 21 (.leaf (-10)) (.leaf (-5)))),
  (.branch 17 (.leaf (-3)) (.leaf (0))),
  (.branch 19 (.branch 11 (.leaf (-14)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 8 (.branch 6 (.branch 5 (.leaf (-18)) (.leaf (-17))) (.branch 7 (.leaf (-16)) (.leaf (-15)))) (.branch 10 (.branch 9 (.leaf (-14)) (.leaf (-13))) (.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-11)) (.leaf (-10)))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1410 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (2)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_1410
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 18 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-4)))),
  (.branch 17 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-15)) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_068_1411 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (2)) (.leaf (1)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (6))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_1411
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 20 (.branch 16 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.leaf (-2)) (.branch 19 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 3 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-12)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-5)) (.leaf (-3))),
  (.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 11 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-11)) (.leaf (-10))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1412 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (2)) (.leaf (1)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (4)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (6)) (.branch 21 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1412
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-13))),
  (.branch 20 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.leaf (-8)) (.leaf (-5))),
  (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-13)) (.branch 11 (.leaf (-12)) (.leaf (-11)))) (.branch 13 (.leaf (-10)) (.branch 14 (.leaf (-9)) (.leaf (-8))))) (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_068_1413 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (6)) (.branch 7 (.leaf (3)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (4)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (5)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (3)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (0)))) (.branch 20 (.leaf (5)) (.branch 21 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1413
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-17)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-16)) (.leaf (-17)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-10))) (.branch 18 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.leaf (0)) (.branch 20 (.leaf (-1)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 15 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 19 (.branch 10 (.leaf (-17)) (.branch 18 (.leaf (-15)) (.leaf (-12)))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-9))) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.leaf (-6)) (.leaf (-5))),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_068_1414 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (4)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (6))))) (.branch 19 (.branch 17 (.leaf (1)) (.branch 18 (.leaf (3)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_1414
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (-1)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 11 (.branch 2 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-10)) (.leaf (-5))))),
  (.branch 13 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (0)))),
  (.branch 9 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 15 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5))))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-4)) (.leaf (-3))),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 11 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-11)) (.leaf (-10))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1415 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (4)) (.leaf (2)))) (.branch 9 (.leaf (6)) (.branch 10 (.leaf (1)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (4)) (.branch 15 (.leaf (5)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (2)))) (.branch 20 (.leaf (6)) (.branch 21 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1415
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-8))) (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 20 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-9)) (.branch 21 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.leaf (0))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_068_1416 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (4))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (2)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (4)) (.leaf (1)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (5)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (2)) (.leaf (3))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (1)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1416
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-12))),
  (.branch 21 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 19 (.branch 18 (.leaf (-10)) (.leaf (-8))) (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.leaf (-6)) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 21 (.leaf (-4)) (.leaf (-2))),
  (.branch 17 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 13 (.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-11)) (.leaf (-10)))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_068_1417 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (5)))))))
  code := certificateD7_1417
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-4)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 16 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4))))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.branch 12 (.leaf (-1)) (.leaf (0))))),
  (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1418 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1418
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 18 (.leaf (-5)) (.leaf (-3))),
  (.branch 20 (.leaf (-4)) (.leaf (-2))),
  (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-10)) (.leaf (-9))) (.branch 14 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-6))))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-14)) (.branch 9 (.leaf (-13)) (.leaf (-12)))) (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_068_1419 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1419
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 15 (.branch 13 (.leaf (5)) (.leaf (6))) (.branch 17 (.leaf (7)) (.branch 20 (.leaf (8)) (.leaf (9)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.branch 16 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 18 (.leaf (-5)) (.leaf (-3))),
  (.branch 19 (.branch 13 (.leaf (-15)) (.leaf (-12))) (.branch 20 (.leaf (-8)) (.leaf (-4)))),
  (.branch 12 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-11)) (.leaf (-10)))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1420 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1420
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 16 (.leaf (-6)) (.leaf (-8)))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 12 (.branch 4 (.leaf (-18)) (.leaf (-17))) (.branch 20 (.leaf (-16)) (.leaf (-8)))),
  (.branch 19 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (-1)),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-16)) (.leaf (-15))) (.branch 8 (.leaf (-14)) (.leaf (-13)))) (.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 12 (.leaf (-10)) (.leaf (-9))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-7)) (.leaf (-6)))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_068_1421 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1421
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 10 (.leaf (-12)) (.branch 14 (.leaf (-13)) (.leaf (-14))))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.leaf (-14)) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 18 (.branch 6 (.leaf (-11)) (.branch 17 (.leaf (-10)) (.leaf (-8)))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4))))),
  (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1422 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1422
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.leaf (0))]
  high := ![(.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.leaf (-11)) (.branch 20 (.leaf (-8)) (.leaf (-5)))),
  (.branch 18 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-13)) (.branch 10 (.leaf (-12)) (.leaf (-11)))) (.branch 12 (.leaf (-10)) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_068_1423 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (6))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (5)))))))
  code := certificateD7_1423
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 10 (.leaf (-12)) (.branch 14 (.leaf (-13)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.leaf (-14)) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 19 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 20 (.leaf (-5)) (.leaf (-4)))),
  (.branch 10 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.branch 6 (.leaf (-11)) (.branch 17 (.leaf (-10)) (.leaf (-8)))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-14)) (.branch 9 (.leaf (-13)) (.leaf (-12)))) (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_068_1424 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (6)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1424
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 14 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 16 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-16)) (.leaf (-15))) (.branch 8 (.leaf (-14)) (.leaf (-13)))) (.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 12 (.leaf (-10)) (.leaf (-9))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_068_1425 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (4)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1425
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 16 (.leaf (-5)) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 17 (.leaf (-3)) (.leaf (-2))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 19 (.branch 8 (.leaf (-7)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-10)) (.leaf (-9))) (.branch 14 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-6))))) (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_068_1426 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1426
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-12)))) (.branch 14 (.leaf (-13)) (.branch 18 (.leaf (-14)) (.leaf (-15))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))),
  (.branch 16 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-14))),
  (.leaf (0))]
  high := ![(.branch 16 (.leaf (-5)) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.leaf (-15)) (.branch 20 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.leaf (-5)) (.leaf (-4))),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-14)) (.branch 9 (.leaf (-13)) (.leaf (-12)))) (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_068_1427 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1427
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-5)))),
  (.branch 19 (.branch 18 (.leaf (-13)) (.leaf (-10))) (.branch 20 (.leaf (-7)) (.leaf (-4)))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-2)),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-16)) (.leaf (-15))) (.branch 8 (.leaf (-14)) (.leaf (-13)))) (.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 12 (.leaf (-10)) (.leaf (-9))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_068_1428 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1428
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-8))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2)))),
  (.branch 20 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-15)) (.branch 8 (.leaf (-14)) (.leaf (-13)))) (.branch 11 (.branch 10 (.leaf (-12)) (.leaf (-11))) (.branch 12 (.leaf (-10)) (.leaf (-9))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_068_1429 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (6)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1429
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 19 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 5 (.leaf (-10)) (.branch 20 (.leaf (-9)) (.leaf (-6)))),
  (.branch 19 (.leaf (-9)) (.branch 20 (.leaf (-7)) (.leaf (-5)))),
  (.leaf (-1)),
  (.branch 17 (.branch 15 (.branch 4 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 15 (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-11)) (.leaf (-10)))) (.branch 13 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-7))))) (.branch 18 (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-5)) (.leaf (-4)))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_068_1430 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (6))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (5)))))))
  code := certificateD7_1430
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 5 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 17 (.leaf (-5)) (.leaf (-4))) (.branch 19 (.leaf (-3)) (.branch 20 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.leaf (-4)) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-14)) (.branch 9 (.leaf (-13)) (.leaf (-12)))) (.branch 12 (.branch 11 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))) (.branch 17 (.branch 15 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.branch 18 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_068_1431 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (5))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1431
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-10)) (.leaf (-12)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0))]
  high := ![(.branch 20 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 13 (.leaf (-12)) (.leaf (-10))) (.branch 20 (.leaf (-7)) (.leaf (-4)))),
  (.branch 19 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 20 (.leaf (-5)) (.leaf (-4)))),
  (.branch 17 (.branch 15 (.branch 4 (.leaf (-15)) (.leaf (-14))) (.branch 16 (.leaf (-12)) (.leaf (-10)))) (.branch 19 (.branch 18 (.leaf (-8)) (.leaf (-6))) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 19 (.leaf (-4)) (.branch 20 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD7_068_1432 : CycleWitness 7 where
  length := 21
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (3)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (5)) (.leaf (2)))))))
  code := certificateD7_1432
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (-4)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 18 (.branch 5 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-13)) (.branch 20 (.leaf (-9)) (.leaf (-5))))),
  (.branch 13 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 19 (.branch 4 (.leaf (-4)) (.leaf (-3))) (.branch 20 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-10)) (.leaf (-8))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 18 (.branch 16 (.leaf (-12)) (.branch 17 (.leaf (-10)) (.leaf (-8)))) (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_068 : Fin 46 → CycleWitness 7 := ![witnessD7_068_1387, witnessD7_068_1388, witnessD7_068_1389, witnessD7_068_1390, witnessD7_068_1391, witnessD7_068_1392, witnessD7_068_1393, witnessD7_068_1394, witnessD7_068_1395, witnessD7_068_1396, witnessD7_068_1397, witnessD7_068_1398, witnessD7_068_1399, witnessD7_068_1400, witnessD7_068_1401, witnessD7_068_1402, witnessD7_068_1403, witnessD7_068_1404, witnessD7_068_1405, witnessD7_068_1406, witnessD7_068_1407, witnessD7_068_1408, witnessD7_068_1409, witnessD7_068_1410, witnessD7_068_1411, witnessD7_068_1412, witnessD7_068_1413, witnessD7_068_1414, witnessD7_068_1415, witnessD7_068_1416, witnessD7_068_1417, witnessD7_068_1418, witnessD7_068_1419, witnessD7_068_1420, witnessD7_068_1421, witnessD7_068_1422, witnessD7_068_1423, witnessD7_068_1424, witnessD7_068_1425, witnessD7_068_1426, witnessD7_068_1427, witnessD7_068_1428, witnessD7_068_1429, witnessD7_068_1430, witnessD7_068_1431, witnessD7_068_1432]
end RealPinwheel.FiveSixths


