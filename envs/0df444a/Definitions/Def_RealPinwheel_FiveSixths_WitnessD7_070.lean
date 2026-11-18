-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_070
-- name    : RealPinwheel_FiveSixths_WitnessD7_070
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:24:03.716112+00:00
-- url     : https://prove2.me/theorems/d7b1ffa2-2095-48b0-a22d-75f71268fb01
-- title:
--   Exact witness block D7_070
-- statement:
--   These exact witnesses represent words 1483 through 1535 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1483–1535; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_070_1482 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 17 (.branch 16 (.leaf (6)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (5)) (.leaf (4)))))))
  code := certificateD7_1482
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 15 (.leaf (-8)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 8 (.leaf (-4)) (.leaf (-3))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_070_1483 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (4))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (5)))))))
  code := certificateD7_1483
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 8 (.branch 2 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 14 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-7))))),
  (.branch 17 (.branch 9 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1484 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (6)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1484
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-14))),
  (.branch 16 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 16 (.leaf (-3)) (.leaf (-2))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_070_1485 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (5)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (2))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1485
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-8)))),
  (.leaf (0))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 3 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 18 (.leaf (-5)) (.branch 19 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0))]
def witnessD7_070_1486 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (4))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (5))))) (.branch 17 (.branch 16 (.leaf (1)) (.leaf (3))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1486
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 9 (.branch 7 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_070_1487 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1487
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-14)) (.leaf (-16)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 9 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-3)) (.leaf (-2))),
  (.branch 7 (.leaf (-5)) (.branch 19 (.leaf (-4)) (.leaf (-3)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1488 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1488
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 13 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 6 (.leaf (-15)) (.leaf (-14)))) (.branch 9 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.leaf (-10))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.leaf (-6)))) (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1489 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (6))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_1489
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-13))),
  (.branch 17 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 19 (.leaf (-4)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-13)) (.branch 9 (.leaf (-12)) (.leaf (-11)))) (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8))))) (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_070_1490 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (0))) (.branch 18 (.leaf (6)) (.branch 19 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1490
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-12))),
  (.branch 18 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 14 (.branch 11 (.branch 9 (.leaf (-12)) (.branch 10 (.leaf (-11)) (.leaf (-10)))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7))))) (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_070_1491 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (0)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (4)) (.leaf (0))) (.branch 18 (.leaf (5)) (.branch 19 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1491
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.leaf (0))]
  high := ![(.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0))]
def witnessD7_070_1492 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (6)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (4)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (5))))) (.branch 17 (.branch 16 (.leaf (2)) (.leaf (1))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1492
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-4)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 6 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 3 (.leaf (-14)) (.branch 10 (.leaf (-13)) (.leaf (-12)))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 17 (.branch 16 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.branch 19 (.leaf (-4)) (.leaf (-3))))),
  (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_070_1493 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (1)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (1)) (.leaf (5))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1493
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 13 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.branch 19 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 8 (.branch 6 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 10 (.branch 9 (.leaf (-12)) (.leaf (-11))) (.branch 11 (.leaf (-10)) (.leaf (-9))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_070_1494 : CycleWitness 7 where
  length := 20
  word := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (3)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (4)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 17 (.branch 16 (.leaf (0)) (.leaf (3))) (.branch 18 (.leaf (2)) (.branch 19 (.leaf (5)) (.leaf (1)))))))
  code := certificateD7_1494
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 19 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 18 (.branch 17 (.leaf (-4)) (.leaf (-3))) (.branch 19 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 17 (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4)))) (.branch 18 (.leaf (-3)) (.branch 19 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1495 : CycleWitness 7 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (6)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1495
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-10)) (.leaf (-20)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 8 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-10))))),
  (.branch 9 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 14 (.leaf (-5)) (.leaf (-4)))),
  (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-13)) (.branch 8 (.leaf (-12)) (.leaf (-11)))) (.branch 10 (.leaf (-10)) (.branch 11 (.leaf (-9)) (.leaf (-8))))) (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1496 : CycleWitness 7 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (5)) (.leaf (0)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1496
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-10)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-4)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 8 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-10))))),
  (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.branch 15 (.branch 4 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 16 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_070_1497 : CycleWitness 7 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (1)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1497
  counts := ![(.branch 9 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 15 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 3 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-9)))),
  (.leaf (-2)),
  (.branch 17 (.branch 7 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-7)) (.leaf (-6)))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_070_1498 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1498
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 11 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.leaf (-6)))),
  (.branch 12 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 8 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 5 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_070_1499 : CycleWitness 7 where
  length := 19
  word := (.branch 10 (.branch 5 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (5))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1499
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-25)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 13 (.branch 5 (.leaf (-18)) (.branch 9 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.leaf (-15)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.branch 4 (.leaf (-25)) (.branch 10 (.leaf (-24)) (.leaf (-23)))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-17)) (.leaf (-14))))),
  (.leaf (-3)),
  (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 8 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1500 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1500
  counts := ![(.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 9 (.leaf (-12)) (.branch 14 (.leaf (-10)) (.leaf (-8)))),
  (.branch 16 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_070_1501 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (5)))))))
  code := certificateD7_1501
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 7 (.leaf (-14)) (.branch 10 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 13 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 11 (.leaf (-16)) (.branch 18 (.leaf (-12)) (.leaf (-6)))),
  (.branch 12 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 17 (.branch 16 (.leaf (-12)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 6 (.leaf (-4)) (.leaf (-3))),
  (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_070_1502 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (3))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1502
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 18 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-9)) (.leaf (-11)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 2 (.leaf (-11)) (.branch 15 (.leaf (-10)) (.leaf (-6)))),
  (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-5)))),
  (.branch 17 (.branch 16 (.leaf (-12)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1503 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1503
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-2)),
  (.branch 13 (.leaf (-2)) (.leaf (0))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-7)) (.leaf (-6)))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_070_1504 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (2))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1504
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 7 (.leaf (-14)) (.branch 10 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 11 (.leaf (-16)) (.branch 18 (.leaf (-12)) (.leaf (-6)))),
  (.branch 16 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 17 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1505 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (4)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1505
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-15)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 11 (.leaf (-17)) (.leaf (-16))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 8 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 12 (.leaf (-5)) (.leaf (-3))),
  (.branch 17 (.branch 10 (.leaf (-11)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 16 (.branch 14 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-2)) (.branch 10 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1506 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1506
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 17 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 16 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-5)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1507 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (5)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (6)) (.leaf (4)))))))
  code := certificateD7_1507
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-15)) (.leaf (-17)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 16 (.branch 11 (.leaf (-17)) (.leaf (-16))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 16 (.branch 15 (.leaf (-15)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 18 (.leaf (-6)) (.leaf (-3))),
  (.branch 17 (.branch 10 (.leaf (-11)) (.leaf (-9))) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.leaf (-2)) (.leaf (0))),
  (.branch 16 (.branch 14 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-8)))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-1))]
def witnessD7_070_1508 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (2)))))))
  code := certificateD7_1508
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 10 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 14 (.leaf (-17)) (.branch 18 (.leaf (-12)) (.leaf (-6)))),
  (.branch 12 (.branch 7 (.leaf (-14)) (.leaf (-13))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-3)) (.leaf (-2))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1509 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1509
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 9 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 13 (.branch 5 (.leaf (-18)) (.branch 9 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.leaf (-15)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 7 (.branch 3 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 18 (.leaf (-6)) (.leaf (-3))),
  (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 11 (.branch 10 (.leaf (-10)) (.leaf (-9))) (.branch 12 (.leaf (-8)) (.branch 13 (.leaf (-7)) (.leaf (-6))))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_070_1510 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1510
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2)))),
  (.branch 3 (.leaf (-3)) (.leaf (-2))),
  (.branch 5 (.leaf (-7)) (.branch 18 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 16 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.leaf (-4)) (.branch 18 (.leaf (-3)) (.leaf (-2))))),
  (.branch 13 (.branch 10 (.branch 8 (.leaf (-12)) (.branch 9 (.leaf (-11)) (.leaf (-10)))) (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-8)) (.leaf (-7))))) (.branch 16 (.branch 14 (.leaf (-6)) (.branch 15 (.leaf (-5)) (.leaf (-4)))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_070_1511 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (3))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (4))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1511
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 10 (.branch 2 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.leaf (-11)) (.branch 18 (.leaf (-10)) (.leaf (-5))))),
  (.branch 16 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 5 (.leaf (-5)) (.branch 12 (.leaf (-4)) (.leaf (-3)))),
  (.branch 17 (.branch 7 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.branch 13 (.leaf (-14)) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 14 (.branch 12 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-7)) (.leaf (-6)))) (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_070_1512 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (1)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1512
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-6)))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 12 (.branch 2 (.leaf (-15)) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 9 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 14 (.leaf (-5)) (.leaf (-4)))),
  (.branch 16 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-9)) (.branch 18 (.leaf (-6)) (.leaf (-3))))),
  (.branch 11 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-3)))),
  (.branch 13 (.leaf (-2)) (.leaf (0))),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-15)) (.branch 6 (.leaf (-14)) (.leaf (-13)))) (.branch 9 (.branch 8 (.leaf (-12)) (.leaf (-11))) (.branch 10 (.leaf (-10)) (.leaf (-9))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-5)) (.leaf (-4))) (.branch 17 (.leaf (-3)) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1513 : CycleWitness 7 where
  length := 19
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (4))) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (2)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (5))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1513
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-15)) (.leaf (-16)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 16 (.branch 6 (.leaf (-18)) (.branch 11 (.leaf (-17)) (.leaf (-16)))) (.branch 17 (.leaf (-12)) (.branch 18 (.leaf (-8)) (.leaf (-4))))),
  (.branch 10 (.branch 5 (.leaf (-3)) (.leaf (-2))) (.branch 15 (.leaf (-1)) (.leaf (0)))),
  (.branch 9 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 14 (.leaf (-5)) (.leaf (-4)))),
  (.branch 8 (.leaf (-5)) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.branch 13 (.branch 12 (.leaf (-16)) (.leaf (-14))) (.branch 14 (.leaf (-12)) (.leaf (-10)))) (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2))))),
  (.branch 17 (.branch 7 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-4)) (.leaf (-2)))),
  (.branch 15 (.branch 13 (.leaf (-7)) (.branch 14 (.leaf (-6)) (.leaf (-5)))) (.branch 17 (.branch 16 (.leaf (-4)) (.leaf (-3))) (.branch 18 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1514 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 14 (.branch 11 (.leaf (0)) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1514
  counts := ![(.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 13 (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 16 (.branch 14 (.leaf (9)) (.leaf (10))) (.branch 17 (.leaf (11)) (.leaf (12)))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.leaf (0))]
  high := ![(.leaf (-2)),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-15)) (.branch 5 (.leaf (-14)) (.leaf (-13)))) (.branch 8 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 9 (.leaf (-10)) (.leaf (-9))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD7_070_1515 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (5))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1515
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 14 (.branch 12 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_070_1516 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1516
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.branch 12 (.leaf (6)) (.leaf (7)))) (.branch 15 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 14 (.branch 3 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-5)))),
  (.branch 10 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_070_1517 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (5)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (3)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_1517
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-11)) (.leaf (-22)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 3 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-16)) (.leaf (-11)))),
  (.branch 4 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (0)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1518 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (5)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1518
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (-5)),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070_1519 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (5))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (1)) (.leaf (6))))))
  code := certificateD7_1519
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_070_1520 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (5))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (6))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1520
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 14 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-15)) (.branch 5 (.leaf (-14)) (.leaf (-13)))) (.branch 8 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 9 (.leaf (-10)) (.leaf (-9))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_070_1521 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1521
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 4 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-7)))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_070_1522 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1522
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 17 (.leaf (-8)) (.leaf (-4))),
  (.branch 16 (.branch 3 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_070_1523 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1523
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 4 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-7)))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_070_1524 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1524
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 8 (.leaf (-15)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 9 (.leaf (-16)) (.branch 17 (.leaf (-14)) (.leaf (-7)))),
  (.branch 16 (.leaf (-11)) (.branch 17 (.leaf (-8)) (.leaf (-5)))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_070_1525 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (6))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1525
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 5 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-2)) (.leaf (0)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 6 (.leaf (-6)) (.leaf (-5))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_070_1526 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (6)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (2)))))))
  code := certificateD7_1526
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.branch 7 (.leaf (-7)) (.leaf (-8))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 17 (.leaf (-8)) (.leaf (-4))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_070_1527 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1527
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 3 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 15 (.branch 5 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_070_1528 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (6))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1528
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 16 (.branch 15 (.leaf (-6)) (.leaf (-5))) (.branch 17 (.leaf (-4)) (.leaf (-3)))),
  (.branch 12 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_070_1529 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (6))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1529
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-8)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 5 (.leaf (-2)) (.leaf (-1))),
  (.branch 6 (.leaf (-11)) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_070_1530 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1530
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_070_1531 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1531
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 16 (.branch 12 (.leaf (-17)) (.leaf (-15))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 3 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.branch 17 (.leaf (-4)) (.leaf (-2))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-13)) (.branch 7 (.leaf (-12)) (.leaf (-11)))) (.branch 9 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_070_1532 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1532
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 11 (.leaf (-16)) (.leaf (-17)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 16 (.branch 12 (.leaf (-17)) (.leaf (-15))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 3 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-5)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_070_1533 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1533
  counts := ![(.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 11 (.leaf (-5)) (.leaf (-4))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_070_1534 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1534
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-6))) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 11 (.branch 7 (.branch 5 (.leaf (-14)) (.branch 6 (.leaf (-13)) (.leaf (-12)))) (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.leaf (-8))))) (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_070 : Fin 53 → CycleWitness 7 := ![witnessD7_070_1482, witnessD7_070_1483, witnessD7_070_1484, witnessD7_070_1485, witnessD7_070_1486, witnessD7_070_1487, witnessD7_070_1488, witnessD7_070_1489, witnessD7_070_1490, witnessD7_070_1491, witnessD7_070_1492, witnessD7_070_1493, witnessD7_070_1494, witnessD7_070_1495, witnessD7_070_1496, witnessD7_070_1497, witnessD7_070_1498, witnessD7_070_1499, witnessD7_070_1500, witnessD7_070_1501, witnessD7_070_1502, witnessD7_070_1503, witnessD7_070_1504, witnessD7_070_1505, witnessD7_070_1506, witnessD7_070_1507, witnessD7_070_1508, witnessD7_070_1509, witnessD7_070_1510, witnessD7_070_1511, witnessD7_070_1512, witnessD7_070_1513, witnessD7_070_1514, witnessD7_070_1515, witnessD7_070_1516, witnessD7_070_1517, witnessD7_070_1518, witnessD7_070_1519, witnessD7_070_1520, witnessD7_070_1521, witnessD7_070_1522, witnessD7_070_1523, witnessD7_070_1524, witnessD7_070_1525, witnessD7_070_1526, witnessD7_070_1527, witnessD7_070_1528, witnessD7_070_1529, witnessD7_070_1530, witnessD7_070_1531, witnessD7_070_1532, witnessD7_070_1533, witnessD7_070_1534]
end RealPinwheel.FiveSixths


