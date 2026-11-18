-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_071
-- name    : RealPinwheel_FiveSixths_WitnessD7_071
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:34:08.507855+00:00
-- url     : https://prove2.me/theorems/ede5a23b-597b-4504-ad1f-dcd675e1fd50
-- title:
--   Exact witness block D7_071
-- statement:
--   These exact witnesses represent words 1536 through 1593 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1536–1593; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_071_1535 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1535
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_071_1536 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1536
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 13 (.branch 9 (.leaf (-14)) (.leaf (-12))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_071_1537 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (6)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (5)))))))
  code := certificateD7_1537
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 17 (.leaf (-7)) (.leaf (-4))))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 4 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_071_1538 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (4)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1538
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 11 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1539 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (6))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1539
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 13 (.branch 2 (.leaf (-13)) (.leaf (-12))) (.branch 17 (.leaf (-10)) (.leaf (-5)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_071_1540 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1540
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 13 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-8)) (.branch 17 (.leaf (-7)) (.leaf (-4))))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-9)) (.leaf (-8))) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-15)) (.branch 5 (.leaf (-14)) (.leaf (-13)))) (.branch 8 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 9 (.leaf (-10)) (.leaf (-9))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1541 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1541
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_071_1542 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (6)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1542
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 16 (.branch 2 (.leaf (-7)) (.leaf (-6))) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.branch 3 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 4 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_071_1543 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (6)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1543
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 11 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 10 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-15)) (.branch 5 (.leaf (-14)) (.leaf (-13)))) (.branch 8 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 9 (.leaf (-10)) (.leaf (-9))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1544 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1544
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 11 (.leaf (-7)) (.leaf (-6))) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1545 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1545
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 7 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-7)))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-15)) (.branch 5 (.leaf (-14)) (.leaf (-13)))) (.branch 8 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 9 (.leaf (-10)) (.leaf (-9))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_071_1546 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1546
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 12 (.branch 9 (.branch 7 (.leaf (-12)) (.branch 8 (.leaf (-11)) (.leaf (-10)))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_071_1547 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (3)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_1547
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 16 (.branch 15 (.leaf (-8)) (.leaf (-6))) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.leaf (-6)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1)),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_071_1548 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (6)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (1))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1548
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 9 (.leaf (-4)) (.leaf (-3))),
  (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 12 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-5)))) (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1549 : CycleWitness 7 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (2))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (6)) (.leaf (3))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1549
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 16 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 16 (.branch 15 (.leaf (-4)) (.leaf (-3))) (.branch 17 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_071_1550 : CycleWitness 7 where
  length := 17
  word := (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1550
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 9 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.leaf (8)) (.branch 16 (.leaf (9)) (.leaf (10)))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 8 (.leaf (-15)) (.branch 15 (.leaf (-13)) (.leaf (-10)))),
  (.branch 14 (.branch 4 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_071_1551 : CycleWitness 7 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (5)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (4))))))
  code := certificateD7_1551
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 9 (.branch 5 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 13 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))),
  (.branch 10 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_071_1552 : CycleWitness 7 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (5)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (6)) (.leaf (2))))))
  code := certificateD7_1552
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-9)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 13 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-13)) (.branch 6 (.leaf (-12)) (.leaf (-11)))) (.branch 8 (.leaf (-10)) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_071_1553 : CycleWitness 7 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (6)) (.leaf (0))) (.branch 16 (.leaf (2)) (.leaf (4))))))
  code := certificateD7_1553
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 13 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 14 (.branch 12 (.leaf (-12)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_071_1554 : CycleWitness 7 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (5))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1554
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.branch 15 (.leaf (-1)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 9 (.branch 5 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 13 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))),
  (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 16 (.leaf (-5)) (.leaf (-4))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_071_1555 : CycleWitness 7 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (5))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (6)) (.leaf (1))))))
  code := certificateD7_1555
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 13 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_071_1556 : CycleWitness 7 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2))))))
  code := certificateD7_1556
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 4 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 5 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-8)))),
  (.branch 11 (.leaf (-4)) (.leaf (-3))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1557 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1557
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-16)) (.branch 7 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-6))))),
  (.branch 15 (.branch 14 (.leaf (-12)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.leaf (-2)) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 15 (.branch 6 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_071_1558 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1558
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 11 (.branch 9 (.leaf (-12)) (.leaf (-13))) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-15)) (.leaf (-8))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 16 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-13)) (.branch 6 (.leaf (-12)) (.leaf (-11)))) (.branch 8 (.leaf (-10)) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_071_1559 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (0)) (.leaf (2)))))))
  code := certificateD7_1559
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 9 (.branch 7 (.leaf (-11)) (.leaf (-12))) (.branch 11 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 12 (.leaf (-14)) (.leaf (-8))),
  (.branch 13 (.branch 11 (.leaf (-14)) (.branch 12 (.leaf (-12)) (.leaf (-10)))) (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_071_1560 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1560
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 4 (.leaf (-16)) (.branch 7 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-6))))),
  (.branch 15 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-7)) (.leaf (-4)))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_071_1561 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1561
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 9 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-7)))),
  (.branch 15 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 16 (.leaf (-4)) (.leaf (-2))),
  (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_071_1562 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1562
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-8)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 8 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.branch 11 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 9 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-13)) (.branch 6 (.leaf (-12)) (.leaf (-11)))) (.branch 8 (.leaf (-10)) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_071_1563 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (6)) (.leaf (4)))))))
  code := certificateD7_1563
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.branch 8 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 14 (.branch 4 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_071_1564 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1564
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 12 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 3 (.leaf (-5)) (.leaf (-4))),
  (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_071_1565 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1565
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 8 (.branch 2 (.leaf (-11)) (.branch 5 (.leaf (-10)) (.leaf (-9)))) (.branch 11 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))),
  (.branch 7 (.leaf (-10)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1566 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_1566
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.branch 8 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 3 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))),
  (.branch 14 (.branch 4 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_071_1567 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1567
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 11 (.leaf (-11)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 5 (.leaf (-2)) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_071_1568 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (6))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (4)))))))
  code := certificateD7_1568
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 2 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 3 (.leaf (-9)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1569 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (6)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1569
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 15 (.branch 10 (.leaf (-15)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 14 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3))))),
  (.branch 4 (.leaf (-3)) (.leaf (-2))),
  (.branch 7 (.leaf (-5)) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1570 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1570
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-4)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 12 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.branch 7 (.leaf (-6)) (.leaf (-5))) (.branch 15 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2))))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 4 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 6 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1571 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1571
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 14 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 10 (.branch 7 (.leaf (-15)) (.leaf (-14))) (.branch 13 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-6))))),
  (.branch 15 (.branch 14 (.leaf (-12)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 12 (.leaf (-12)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_071_1572 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (6)))))))
  code := certificateD7_1572
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 11 (.leaf (-12)) (.leaf (-13)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-13)) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 10 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 4 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_071_1573 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1573
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 15 (.branch 6 (.leaf (-14)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 14 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-2)),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-13)) (.branch 6 (.leaf (-12)) (.leaf (-11)))) (.branch 8 (.leaf (-10)) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1574 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1574
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 12 (.branch 8 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1575 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1575
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 15 (.leaf (-15)) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 11 (.leaf (-4)) (.leaf (-3))),
  (.branch 16 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1576 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1576
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-6)) (.leaf (-8)))),
  (.leaf (0))]
  high := ![(.branch 13 (.branch 10 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-12)) (.leaf (-6)))),
  (.branch 13 (.branch 3 (.leaf (-13)) (.branch 12 (.leaf (-12)) (.leaf (-10)))) (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6)))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD7_071_1577 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (6)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1577
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 12 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.branch 8 (.leaf (-13)) (.leaf (-12))) (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 15 (.branch 6 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_071_1578 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (5)) (.leaf (1)))))))
  code := certificateD7_1578
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 16 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 15 (.branch 6 (.leaf (-14)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.branch 7 (.leaf (-10)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 14 (.branch 4 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-7)) (.leaf (-6)))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_071_1579 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (6)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (5)) (.branch 16 (.leaf (1)) (.leaf (2)))))))
  code := certificateD7_1579
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 14 (.branch 2 (.leaf (-14)) (.branch 8 (.leaf (-13)) (.leaf (-12)))) (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3))))),
  (.branch 5 (.leaf (-5)) (.branch 11 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 9 (.branch 3 (.leaf (-11)) (.leaf (-10))) (.branch 15 (.leaf (-9)) (.branch 16 (.leaf (-6)) (.leaf (-3))))),
  (.branch 14 (.branch 12 (.leaf (-12)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 6 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1580 : CycleWitness 7 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (4))) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1580
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.branch 16 (.leaf (-3)) (.leaf (-4))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0))]
  high := ![(.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-4)),
  (.branch 14 (.branch 12 (.leaf (-12)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.leaf (-4)) (.leaf (-2))),
  (.branch 13 (.branch 11 (.leaf (-14)) (.branch 12 (.leaf (-12)) (.leaf (-10)))) (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0))]
def witnessD7_071_1581 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (4))))))
  code := certificateD7_1581
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_071_1582 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (6))))) (.branch 12 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 13 (.leaf (2)) (.branch 15 (.leaf (0)) (.leaf (5))))))
  code := certificateD7_1582
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 9 (.leaf (5)) (.branch 10 (.leaf (6)) (.leaf (7)))) (.branch 14 (.leaf (8)) (.branch 15 (.leaf (9)) (.leaf (10)))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_071_1583 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (6))) (.branch 15 (.leaf (0)) (.leaf (4))))))
  code := certificateD7_1583
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.leaf (-1)),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_071_1584 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1584
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 13 (.leaf (-12)) (.leaf (-7))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-12)) (.branch 6 (.leaf (-11)) (.leaf (-10)))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_071_1585 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (5))))))
  code := certificateD7_1585
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 13 (.leaf (-12)) (.leaf (-7))),
  (.branch 14 (.branch 8 (.leaf (-11)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_071_1586 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (6)) (.leaf (2))))))
  code := certificateD7_1586
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.leaf (-2)) (.leaf (0))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-12)) (.branch 6 (.leaf (-11)) (.leaf (-10)))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_071_1587 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (6))))))
  code := certificateD7_1587
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-1)),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_071_1588 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (4))))))
  code := certificateD7_1588
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.leaf (-8)) (.leaf (-5))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-12)) (.branch 6 (.leaf (-11)) (.leaf (-10)))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_071_1589 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (6))))))
  code := certificateD7_1589
  counts := ![(.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 2 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7)))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_071_1590 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4))))))
  code := certificateD7_1590
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_071_1591 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (6))))))
  code := certificateD7_1591
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-12)) (.branch 6 (.leaf (-11)) (.leaf (-10)))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD7_071_1592 : CycleWitness 7 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (6))))))
  code := certificateD7_1592
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.leaf (-8)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_071 : Fin 58 → CycleWitness 7 := ![witnessD7_071_1535, witnessD7_071_1536, witnessD7_071_1537, witnessD7_071_1538, witnessD7_071_1539, witnessD7_071_1540, witnessD7_071_1541, witnessD7_071_1542, witnessD7_071_1543, witnessD7_071_1544, witnessD7_071_1545, witnessD7_071_1546, witnessD7_071_1547, witnessD7_071_1548, witnessD7_071_1549, witnessD7_071_1550, witnessD7_071_1551, witnessD7_071_1552, witnessD7_071_1553, witnessD7_071_1554, witnessD7_071_1555, witnessD7_071_1556, witnessD7_071_1557, witnessD7_071_1558, witnessD7_071_1559, witnessD7_071_1560, witnessD7_071_1561, witnessD7_071_1562, witnessD7_071_1563, witnessD7_071_1564, witnessD7_071_1565, witnessD7_071_1566, witnessD7_071_1567, witnessD7_071_1568, witnessD7_071_1569, witnessD7_071_1570, witnessD7_071_1571, witnessD7_071_1572, witnessD7_071_1573, witnessD7_071_1574, witnessD7_071_1575, witnessD7_071_1576, witnessD7_071_1577, witnessD7_071_1578, witnessD7_071_1579, witnessD7_071_1580, witnessD7_071_1581, witnessD7_071_1582, witnessD7_071_1583, witnessD7_071_1584, witnessD7_071_1585, witnessD7_071_1586, witnessD7_071_1587, witnessD7_071_1588, witnessD7_071_1589, witnessD7_071_1590, witnessD7_071_1591, witnessD7_071_1592]
end RealPinwheel.FiveSixths


