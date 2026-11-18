-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_067
-- name    : RealPinwheel_FiveSixths_WitnessD7_067
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:18:19.837893+00:00
-- url     : https://prove2.me/theorems/1b082b90-846a-4218-b25a-cba81b55c2a6
-- title:
--   Exact witness block D7_067
-- statement:
--   These exact witnesses represent words 1346 through 1387 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1346–1387; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_067_1345 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1345
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 21 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 23 (.leaf (11)) (.leaf (12)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_067_1346 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (5)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1346
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 20 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 20 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 23 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 20 (.branch 18 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_067_1347 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (1)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (5))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1347
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 14 (.leaf (5)) (.leaf (6))) (.branch 19 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (9)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 10 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 20 (.leaf (-7)) (.branch 23 (.leaf (-6)) (.leaf (-3)))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_067_1348 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1348
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_067_1349 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (5)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (6)) (.leaf (4)))))))
  code := certificateD7_1349
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-13))),
  (.branch 23 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 17 (.branch 14 (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))) (.branch 15 (.leaf (-10)) (.branch 16 (.leaf (-9)) (.leaf (-8))))) (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_067_1350 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (6)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1350
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-15))),
  (.branch 21 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_067_1351 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1351
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 21 (.leaf (-20)) (.leaf (-21)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 10 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-14)) (.leaf (-7)))),
  (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.leaf (-2)))),
  (.branch 18 (.leaf (-3)) (.leaf (-2))),
  (.branch 6 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_067_1352 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1352
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-12))),
  (.leaf (0))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.branch 15 (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_067_1353 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (4)) (.leaf (3)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1353
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-14)) (.leaf (-17)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-10))),
  (.branch 22 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-18)))]
  high := ![(.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 12 (.leaf (-17)) (.leaf (-16))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 9 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 14 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_067_1354 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (3)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1354
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 21 (.leaf (-20)) (.leaf (-21)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-9)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 13 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 22 (.leaf (-21)) (.branch 23 (.leaf (-14)) (.leaf (-7)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 18 (.branch 15 (.branch 14 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.branch 17 (.leaf (-8)) (.leaf (-7))))) (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 9 (.branch 7 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 8 (.leaf (-17)) (.leaf (-16)))) (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_067_1355 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (0)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (6)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1355
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-17))) (.branch 14 (.leaf (-20)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 22 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-14)) (.leaf (-7)))),
  (.branch 10 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-7)))),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1356 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (4)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (6)) (.leaf (0)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1356
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 14 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 24 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 20 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_067_1357 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1357
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-19)) (.leaf (-22)))),
  (.branch 2 (.leaf (0)) (.leaf (-14))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-16))),
  (.branch 19 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 21 (.branch 11 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 13 (.branch 3 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 19 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1358 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (2)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (6)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (1)) (.leaf (4)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_1358
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 22 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-20))),
  (.branch 17 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 19 (.leaf (-18)) (.branch 23 (.leaf (-14)) (.leaf (-7)))),
  (.branch 17 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (0)))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 9 (.branch 6 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 7 (.leaf (-18)) (.branch 8 (.leaf (-17)) (.leaf (-16))))) (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1359 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (1)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (2)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1359
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 23 (.leaf (-3)) (.leaf (-2)))),
  (.branch 16 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 5 (.leaf (-9)) (.branch 19 (.leaf (-8)) (.leaf (-7)))) (.branch 22 (.branch 21 (.leaf (-6)) (.leaf (-5))) (.branch 23 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_067_1360 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (3)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (1)) (.leaf (0)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1360
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 13 (.leaf (5)) (.branch 16 (.leaf (6)) (.leaf (7)))) (.branch 21 (.leaf (8)) (.branch 23 (.leaf (9)) (.leaf (10)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-17))),
  (.branch 19 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 14 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-17)) (.leaf (-16))) (.branch 10 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.branch 12 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-10))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1361 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (6)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (3)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (4)) (.leaf (0)))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 22 (.leaf (4)) (.branch 23 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1361
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-23)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 16 (.branch 6 (.leaf (-23)) (.branch 11 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-15))) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 18 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_067_1362 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (3)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (4)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1362
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 19 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-20)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-1)),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 9 (.branch 6 (.branch 5 (.leaf (-20)) (.leaf (-19))) (.branch 7 (.leaf (-18)) (.branch 8 (.leaf (-17)) (.leaf (-16))))) (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_067_1363 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (1)) (.leaf (0)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 22 (.leaf (5)) (.branch 23 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1363
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-14)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.branch 7 (.leaf (-18)) (.branch 12 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 6 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-5)))),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1364 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (2)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (4)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1364
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 18 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 20 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 12 (.branch 10 (.branch 9 (.leaf (-16)) (.leaf (-15))) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_067_1365 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (6)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (5)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1365
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 22 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-14)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 18 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.branch 20 (.leaf (-1)) (.leaf (0))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_067_1366 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (1)) (.leaf (3)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (0))))) (.branch 21 (.branch 19 (.leaf (3)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (6)) (.branch 23 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1366
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-14))),
  (.branch 22 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 17 (.branch 13 (.branch 11 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 15 (.branch 14 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-9)) (.leaf (-8))))) (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_067_1367 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (1)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (1)) (.leaf (2))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1367
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD7_067_1368 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (6)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (3)))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (5))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 22 (.leaf (0)) (.branch 23 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1368
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.branch 22 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 7 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-12)))) (.branch 22 (.leaf (-10)) (.branch 23 (.leaf (-8)) (.leaf (-6))))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 21 (.branch 19 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6)))) (.branch 22 (.leaf (-5)) (.branch 23 (.leaf (-4)) (.leaf (-3))))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-15)) (.branch 11 (.leaf (-14)) (.leaf (-13)))) (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))) (.branch 20 (.branch 18 (.branch 17 (.leaf (-8)) (.leaf (-7))) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_067_1369 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (1)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1369
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-18))),
  (.branch 18 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 15 (.branch 10 (.branch 8 (.branch 7 (.leaf (-18)) (.leaf (-17))) (.branch 9 (.leaf (-16)) (.leaf (-15)))) (.branch 12 (.branch 11 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-10)))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 18 (.leaf (-7)) (.leaf (-6)))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1370 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (5)) (.leaf (1)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (4)) (.branch 14 (.leaf (2)) (.leaf (0)))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (6))))) (.branch 21 (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 22 (.leaf (1)) (.branch 23 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1370
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-19)) (.leaf (-23)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-9)) (.leaf (-13)))),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 19 (.leaf (-11)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 16 (.branch 6 (.leaf (-23)) (.branch 11 (.leaf (-22)) (.leaf (-21)))) (.branch 22 (.branch 21 (.leaf (-20)) (.leaf (-15))) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 13 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 18 (.leaf (-11)) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 21 (.branch 20 (.leaf (-14)) (.leaf (-12))) (.branch 22 (.leaf (-10)) (.branch 23 (.leaf (-8)) (.leaf (-6))))),
  (.leaf (0)),
  (.branch 22 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 21 (.branch 19 (.leaf (-6)) (.branch 20 (.leaf (-5)) (.leaf (-4)))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1371 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1371
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-19))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 17 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 12 (.branch 2 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 22 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 14 (.branch 9 (.branch 7 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 8 (.leaf (-17)) (.leaf (-16)))) (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-14))) (.branch 12 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-11)))))) (.branch 19 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.branch 18 (.leaf (-7)) (.leaf (-6))))) (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1372 : CycleWitness 7 where
  length := 24
  word := (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (3)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (1)) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (1))))) (.branch 21 (.branch 19 (.leaf (4)) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 22 (.leaf (3)) (.branch 23 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1372
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 23 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 22 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-19))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 12 (.branch 2 (.leaf (-19)) (.branch 7 (.leaf (-18)) (.leaf (-17)))) (.branch 22 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))),
  (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 22 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 18 (.leaf (-7)) (.branch 19 (.leaf (-6)) (.leaf (-5)))) (.branch 22 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 23 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_067_1373 : CycleWitness 7 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (3)))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (6)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1373
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 16 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-15)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.leaf (-14))),
  (.branch 20 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 19 (.branch 16 (.leaf (-18)) (.leaf (-17))) (.branch 22 (.leaf (-16)) (.leaf (-8)))),
  (.branch 17 (.leaf (-4)) (.leaf (-3))),
  (.branch 20 (.branch 4 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.branch 16 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 6 (.leaf (-13)) (.branch 18 (.leaf (-12)) (.leaf (-10)))) (.branch 21 (.branch 20 (.leaf (-8)) (.leaf (-6))) (.branch 22 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-14)) (.branch 11 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.branch 13 (.leaf (-11)) (.leaf (-10))) (.branch 15 (.leaf (-9)) (.leaf (-8))))) (.branch 19 (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.leaf (-3)) (.branch 22 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_067_1374 : CycleWitness 7 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (5))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (2)) (.leaf (0)))) (.branch 9 (.leaf (3)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (6)) (.leaf (2))))) (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (4)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1374
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-16)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))),
  (.branch 9 (.leaf (0)) (.leaf (-14))),
  (.branch 20 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-18))),
  (.branch 16 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.branch 5 (.leaf (-18)) (.leaf (-17))) (.branch 22 (.leaf (-14)) (.leaf (-7)))),
  (.branch 20 (.branch 16 (.leaf (-5)) (.leaf (-4))) (.branch 21 (.leaf (-2)) (.leaf (0)))),
  (.branch 13 (.branch 8 (.leaf (-7)) (.leaf (-6))) (.branch 18 (.leaf (-5)) (.leaf (-4)))),
  (.branch 16 (.branch 12 (.branch 10 (.leaf (-14)) (.branch 11 (.leaf (-13)) (.leaf (-12)))) (.branch 14 (.branch 13 (.leaf (-11)) (.leaf (-10))) (.branch 15 (.leaf (-9)) (.leaf (-8))))) (.branch 19 (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.leaf (-3)) (.branch 22 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 9 (.branch 7 (.branch 6 (.leaf (-18)) (.leaf (-17))) (.branch 8 (.leaf (-16)) (.leaf (-15)))) (.branch 11 (.branch 10 (.leaf (-14)) (.leaf (-13))) (.branch 12 (.leaf (-12)) (.branch 13 (.leaf (-11)) (.leaf (-10)))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-7)) (.leaf (-6)))) (.branch 20 (.branch 19 (.leaf (-5)) (.leaf (-4))) (.branch 21 (.leaf (-3)) (.branch 22 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1375 : CycleWitness 7 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (5)) (.branch 10 (.leaf (1)) (.leaf (0)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (3)) (.branch 13 (.leaf (6)) (.leaf (0)))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (1)) (.branch 19 (.leaf (5)) (.leaf (0)))) (.branch 21 (.leaf (3)) (.branch 22 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1375
  counts := ![(.branch 11 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 17 (.branch 14 (.leaf (4)) (.leaf (5))) (.branch 20 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 7 (.leaf (-18)) (.branch 20 (.leaf (-20)) (.leaf (-21))))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-20)))),
  (.branch 13 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 21 (.leaf (-21)) (.branch 22 (.leaf (-14)) (.leaf (-7)))),
  (.branch 19 (.branch 3 (.leaf (-17)) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.branch 20 (.leaf (-12)) (.leaf (-9))) (.branch 22 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-2)),
  (.branch 13 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.leaf (-7)))),
  (.branch 16 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0))))),
  (.branch 20 (.branch 10 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-17)) (.branch 22 (.leaf (-15)) (.leaf (-13))))),
  (.branch 18 (.branch 15 (.branch 14 (.leaf (-10)) (.leaf (-9))) (.branch 16 (.leaf (-8)) (.branch 17 (.leaf (-7)) (.leaf (-6))))) (.branch 20 (.branch 19 (.leaf (-5)) (.leaf (-4))) (.branch 21 (.leaf (-3)) (.branch 22 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_067_1376 : CycleWitness 7 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (5)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (3)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (4)) (.branch 13 (.leaf (0)) (.leaf (2)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (6)) (.leaf (0))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 21 (.leaf (0)) (.branch 22 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1376
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 17 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 21 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 15 (.leaf (3)) (.branch 20 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-17))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 10 (.leaf (-10)) (.leaf (-12)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 22 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 10 (.branch 2 (.leaf (-17)) (.branch 6 (.leaf (-16)) (.leaf (-15)))) (.branch 18 (.branch 14 (.leaf (-14)) (.leaf (-13))) (.branch 22 (.leaf (-12)) (.leaf (-6))))),
  (.branch 16 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-7)) (.leaf (-4))))),
  (.leaf (-3)),
  (.branch 20 (.branch 4 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 15 (.branch 11 (.branch 9 (.branch 8 (.leaf (-16)) (.leaf (-15))) (.branch 10 (.leaf (-14)) (.leaf (-13)))) (.branch 13 (.branch 12 (.leaf (-12)) (.leaf (-11))) (.branch 14 (.leaf (-10)) (.leaf (-9))))) (.branch 19 (.branch 17 (.branch 16 (.leaf (-8)) (.leaf (-7))) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1377 : CycleWitness 7 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (5)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (3)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (1))))) (.branch 20 (.branch 18 (.leaf (6)) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 21 (.leaf (2)) (.branch 22 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1377
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 21 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-17))),
  (.branch 18 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-12)) (.leaf (-6)))),
  (.branch 8 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))),
  (.branch 16 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.branch 4 (.leaf (-14)) (.branch 12 (.leaf (-13)) (.leaf (-12)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-6)) (.leaf (-3))))),
  (.branch 15 (.leaf (-2)) (.branch 16 (.leaf (-1)) (.leaf (0)))),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-17)) (.leaf (-16))) (.branch 9 (.leaf (-15)) (.leaf (-14)))) (.branch 12 (.branch 11 (.leaf (-13)) (.leaf (-12))) (.branch 13 (.leaf (-11)) (.leaf (-10))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-9)) (.leaf (-8))) (.branch 17 (.leaf (-7)) (.leaf (-6)))) (.branch 20 (.branch 19 (.leaf (-5)) (.leaf (-4))) (.branch 21 (.leaf (-3)) (.branch 22 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 20 (.branch 19 (.leaf (-5)) (.leaf (-4))) (.branch 21 (.leaf (-3)) (.branch 22 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1378 : CycleWitness 7 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (2)) (.branch 7 (.leaf (1)) (.leaf (4)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (5)))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (2))))) (.branch 20 (.branch 18 (.leaf (3)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 21 (.leaf (6)) (.branch 22 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1378
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 19 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-17)) (.leaf (-20)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-15)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-14)) (.leaf (-16)))),
  (.branch 15 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-10)))),
  (.branch 21 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 17 (.branch 13 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-12)) (.leaf (-6))))),
  (.branch 20 (.branch 8 (.leaf (-18)) (.branch 14 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-8)) (.leaf (-4))))),
  (.branch 12 (.leaf (-2)) (.branch 18 (.leaf (-1)) (.leaf (0)))),
  (.branch 20 (.branch 11 (.leaf (-16)) (.branch 19 (.leaf (-15)) (.leaf (-12)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-2)),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-7)))) (.branch 20 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 21 (.leaf (-4)) (.branch 22 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 22 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_067_1379 : CycleWitness 7 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (2)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (5)) (.leaf (1)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (4)))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2))))) (.branch 20 (.branch 18 (.leaf (3)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 21 (.leaf (6)) (.branch 22 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1379
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 22 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-19)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.leaf (-13))),
  (.branch 21 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-12)) (.leaf (-6)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 8 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.branch 18 (.leaf (-8)) (.leaf (-7))))),
  (.branch 20 (.branch 7 (.leaf (-11)) (.branch 19 (.leaf (-10)) (.leaf (-8)))) (.branch 21 (.leaf (-6)) (.branch 22 (.leaf (-4)) (.leaf (-2))))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 17 (.leaf (-8)) (.leaf (-7)))) (.branch 20 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 21 (.leaf (-4)) (.branch 22 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 16 (.branch 13 (.branch 11 (.leaf (-13)) (.branch 12 (.leaf (-12)) (.leaf (-11)))) (.branch 14 (.leaf (-10)) (.branch 15 (.leaf (-9)) (.leaf (-8))))) (.branch 19 (.branch 17 (.leaf (-7)) (.branch 18 (.leaf (-6)) (.leaf (-5)))) (.branch 21 (.branch 20 (.leaf (-4)) (.leaf (-3))) (.branch 22 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_067_1380 : CycleWitness 7 where
  length := 23
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (6)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (5)))))) (.branch 17 (.branch 14 (.branch 12 (.leaf (4)) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (3)) (.leaf (1))))) (.branch 20 (.branch 18 (.leaf (2)) (.branch 19 (.leaf (0)) (.leaf (4)))) (.branch 21 (.leaf (1)) (.branch 22 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1380
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 19 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 17 (.leaf (3)) (.branch 21 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 9 (.leaf (-13)) (.leaf (-15)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 21 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-7)) (.leaf (-11))))]
  high := ![(.branch 20 (.branch 10 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-13)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-7)) (.leaf (-4))))),
  (.branch 22 (.leaf (-4)) (.leaf (-3))),
  (.branch 19 (.branch 3 (.leaf (-17)) (.branch 11 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.branch 20 (.leaf (-12)) (.leaf (-9))) (.branch 22 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 13 (.branch 5 (.leaf (-11)) (.leaf (-10))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-2)),
  (.branch 19 (.branch 17 (.branch 16 (.leaf (-11)) (.leaf (-10))) (.branch 18 (.leaf (-9)) (.leaf (-8)))) (.branch 21 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 22 (.leaf (-5)) (.leaf (-4)))))]
def witnessD7_067_1381 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 5 (.leaf (0)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (5))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1381
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 9 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (7)) (.leaf (8))) (.branch 15 (.leaf (9)) (.leaf (10)))) (.branch 20 (.branch 18 (.leaf (11)) (.leaf (12))) (.branch 21 (.leaf (13)) (.leaf (14)))))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-9)) (.leaf (-7))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_067_1382 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (5)) (.leaf (0))))) (.branch 8 (.branch 7 (.leaf (1)) (.leaf (0))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))))) (.branch 17 (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (6)) (.leaf (0))))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (4)) (.branch 21 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1382
  counts := ![(.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (5))))) (.branch 15 (.branch 12 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))) (.branch 19 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-17))),
  (.branch 16 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 16 (.branch 14 (.leaf (-10)) (.leaf (-9))) (.branch 18 (.leaf (-8)) (.branch 20 (.leaf (-7)) (.leaf (-6))))),
  (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 9 (.branch 7 (.branch 6 (.leaf (-17)) (.leaf (-16))) (.branch 8 (.leaf (-15)) (.leaf (-14)))) (.branch 11 (.branch 10 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-11)) (.leaf (-10))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-9)) (.leaf (-8))) (.branch 16 (.leaf (-7)) (.leaf (-6)))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_067_1383 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (4)))) (.branch 20 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1383
  counts := ![(.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 18 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 21 (.leaf (-8)) (.leaf (-4)))),
  (.branch 16 (.leaf (-6)) (.branch 19 (.leaf (-5)) (.leaf (-4)))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 11 (.branch 9 (.leaf (-14)) (.branch 10 (.leaf (-13)) (.leaf (-12)))) (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.leaf (-8))))) (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_067_1384 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (1)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (2)) (.leaf (0)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (1)) (.branch 15 (.leaf (0)) (.leaf (4))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1384
  counts := ![(.branch 11 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))) (.branch 17 (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))) (.branch 19 (.leaf (9)) (.branch 21 (.leaf (10)) (.leaf (11)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 16 (.leaf (0)) (.leaf (-6))),
  (.branch 12 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 9 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 15 (.leaf (-9)) (.branch 21 (.leaf (-8)) (.leaf (-5))))),
  (.branch 19 (.branch 11 (.leaf (-10)) (.leaf (-9))) (.branch 20 (.leaf (-7)) (.branch 21 (.leaf (-5)) (.leaf (-3))))),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-7)) (.leaf (-6))))) (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_067_1385 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (5)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (0))))) (.branch 19 (.branch 17 (.leaf (4)) (.branch 18 (.leaf (1)) (.leaf (0)))) (.branch 20 (.leaf (2)) (.branch 21 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1385
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 16 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 19 (.leaf (8)) (.branch 21 (.leaf (9)) (.leaf (10)))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 20 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-16))),
  (.branch 17 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-8)) (.leaf (-5))),
  (.branch 20 (.branch 19 (.leaf (-8)) (.leaf (-6))) (.branch 21 (.leaf (-4)) (.leaf (-2)))),
  (.branch 21 (.leaf (-4)) (.leaf (-2))),
  (.branch 14 (.branch 10 (.branch 8 (.branch 7 (.leaf (-16)) (.leaf (-15))) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 19 (.branch 18 (.leaf (-5)) (.leaf (-4))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_067_1386 : CycleWitness 7 where
  length := 22
  word := (.branch 11 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (5)) (.leaf (0)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))))) (.branch 16 (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.branch 15 (.leaf (2)) (.leaf (1))))) (.branch 19 (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (0)))) (.branch 20 (.leaf (1)) (.branch 21 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1386
  counts := ![(.branch 10 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))) (.branch 17 (.branch 12 (.leaf (5)) (.branch 14 (.leaf (6)) (.leaf (7)))) (.branch 19 (.leaf (8)) (.branch 21 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 16 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 20 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-15))),
  (.branch 18 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 15 (.leaf (-7)) (.leaf (-5))),
  (.branch 17 (.leaf (-7)) (.branch 21 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.branch 16 (.leaf (-7)) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 13 (.branch 12 (.leaf (-11)) (.leaf (-10))) (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-8)) (.leaf (-7))))) (.branch 19 (.branch 17 (.leaf (-6)) (.branch 18 (.leaf (-5)) (.leaf (-4)))) (.branch 20 (.leaf (-3)) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 14 (.branch 10 (.branch 8 (.leaf (-15)) (.branch 9 (.leaf (-14)) (.leaf (-13)))) (.branch 12 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-9))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-7))) (.branch 17 (.leaf (-6)) (.leaf (-5)))) (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_067 : Fin 42 → CycleWitness 7 := ![witnessD7_067_1345, witnessD7_067_1346, witnessD7_067_1347, witnessD7_067_1348, witnessD7_067_1349, witnessD7_067_1350, witnessD7_067_1351, witnessD7_067_1352, witnessD7_067_1353, witnessD7_067_1354, witnessD7_067_1355, witnessD7_067_1356, witnessD7_067_1357, witnessD7_067_1358, witnessD7_067_1359, witnessD7_067_1360, witnessD7_067_1361, witnessD7_067_1362, witnessD7_067_1363, witnessD7_067_1364, witnessD7_067_1365, witnessD7_067_1366, witnessD7_067_1367, witnessD7_067_1368, witnessD7_067_1369, witnessD7_067_1370, witnessD7_067_1371, witnessD7_067_1372, witnessD7_067_1373, witnessD7_067_1374, witnessD7_067_1375, witnessD7_067_1376, witnessD7_067_1377, witnessD7_067_1378, witnessD7_067_1379, witnessD7_067_1380, witnessD7_067_1381, witnessD7_067_1382, witnessD7_067_1383, witnessD7_067_1384, witnessD7_067_1385, witnessD7_067_1386]
end RealPinwheel.FiveSixths


