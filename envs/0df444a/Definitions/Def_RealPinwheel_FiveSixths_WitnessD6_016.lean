-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_016
-- name    : RealPinwheel_FiveSixths_WitnessD6_016
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:30:05.189211+00:00
-- url     : https://prove2.me/theorems/df10508e-509c-4526-a770-d08182767dfb
-- title:
--   Exact witness block D6_016
-- statement:
--   These exact witnesses represent words 530 through 594 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 530–594; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_016_529 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (5))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (2)))))))
  code := certificateD6_529
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 15 (.branch 8 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 15 (.branch 14 (.leaf (-12)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 10 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 6 (.leaf (-5)) (.leaf (-4))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_530 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))))))
  code := certificateD6_530
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 12 (.branch 8 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_531 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))))))
  code := certificateD6_531
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 9 (.branch 2 (.leaf (-12)) (.leaf (-11))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 15 (.leaf (-8)) (.branch 16 (.leaf (-6)) (.leaf (-4)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 10 (.branch 6 (.branch 4 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 8 (.branch 7 (.leaf (-11)) (.leaf (-10))) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_016_532 : CycleWitness 6 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (1)))))))
  code := certificateD6_532
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 13 (.leaf (-3)) (.leaf (0))),
  (.branch 11 (.leaf (-11)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 14 (.branch 12 (.leaf (-12)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_533 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 5 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.leaf (4)) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.leaf (5)) (.branch 15 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_533
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 9 (.leaf (5)) (.branch 10 (.leaf (6)) (.leaf (7)))) (.branch 13 (.leaf (8)) (.branch 15 (.leaf (9)) (.leaf (10)))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 14 (.leaf (-7)) (.leaf (-5))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_016_534 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_534
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_016_535 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (3))))) (.branch 12 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (3))))))
  code := certificateD6_535
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_016_536 : CycleWitness 6 where
  length := 16
  word := (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (5))) (.branch 15 (.leaf (0)) (.leaf (1))))))
  code := certificateD6_536
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 12 (.branch 10 (.leaf (-15)) (.leaf (-13))) (.branch 14 (.leaf (-11)) (.leaf (-9)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_016_537 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (1))))))
  code := certificateD6_537
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 10 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-4)))),
  (.branch 7 (.leaf (-2)) (.leaf (0))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_016_538 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (2))))))
  code := certificateD6_538
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 10 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-4)))),
  (.branch 5 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_539 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_539
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_540 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_540
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-12)) (.branch 6 (.leaf (-11)) (.leaf (-10)))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD6_016_541 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (5))))))
  code := certificateD6_541
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-11)) (.branch 7 (.leaf (-13)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 8 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-7)))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_542 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (4))))))
  code := certificateD6_542
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 6 (.leaf (-13)) (.branch 13 (.leaf (-12)) (.leaf (-7)))),
  (.branch 14 (.branch 8 (.leaf (-11)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.leaf (-6)) (.leaf (-3))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_543 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_543
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.leaf (-8)) (.leaf (-5))),
  (.branch 14 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_544 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3))))))
  code := certificateD6_544
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 5 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_545 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (5))))))
  code := certificateD6_545
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 8 (.leaf (-13)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_546 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3))))))
  code := certificateD6_546
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 8 (.leaf (-7)) (.branch 11 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 12 (.leaf (-9)) (.leaf (-5))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_547 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (4))))))
  code := certificateD6_547
  counts := ![(.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 2 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7)))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_548 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (4)) (.leaf (3))))))
  code := certificateD6_548
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 14 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.leaf (-2)) (.leaf (0))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_549 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (5))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_549
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 10 (.branch 7 (.leaf (-6)) (.leaf (-5))) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 14 (.branch 8 (.leaf (-11)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 6 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_550 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_550
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 10 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_551 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_551
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 10 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_552 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (3))))))
  code := certificateD6_552
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 11 (.leaf (-14)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1))]
def witnessD6_016_553 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3))))))
  code := certificateD6_553
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_554 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3))))))
  code := certificateD6_554
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.branch 10 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 11 (.leaf (-14)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 4 (.leaf (-5)) (.branch 10 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_555 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4))))))
  code := certificateD6_555
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.leaf (-8)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_556 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3))))))
  code := certificateD6_556
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.leaf (-8)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-12)) (.branch 6 (.leaf (-11)) (.leaf (-10)))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_016_557 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (4))))))
  code := certificateD6_557
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 5 (.leaf (-12)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.branch 8 (.leaf (-11)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 13 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_016_558 : CycleWitness 6 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (5)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (2)) (.leaf (4))))))
  code := certificateD6_558
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 13 (.leaf (-12)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 5 (.leaf (-4)) (.leaf (-3))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_559 : CycleWitness 6 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_559
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 9 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_560 : CycleWitness 6 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2))))))
  code := certificateD6_560
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 4 (.leaf (-12)) (.leaf (-13)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 5 (.leaf (-13)) (.branch 14 (.leaf (-12)) (.leaf (-7)))),
  (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 13 (.leaf (-4)) (.branch 14 (.leaf (-3)) (.leaf (-2)))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_016_561 : CycleWitness 6 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (3)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (1)) (.leaf (2))))))
  code := certificateD6_561
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 13 (.branch 3 (.leaf (-18)) (.leaf (-17))) (.branch 14 (.leaf (-13)) (.leaf (-9)))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 12 (.branch 11 (.leaf (-6)) (.leaf (-5))) (.branch 13 (.leaf (-4)) (.branch 14 (.leaf (-3)) (.leaf (-2))))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_016_562 : CycleWitness 6 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1))))))
  code := certificateD6_562
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 11 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 14 (.leaf (-13)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_016_563 : CycleWitness 6 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (1))))))
  code := certificateD6_563
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 7 (.branch 3 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_564 : CycleWitness 6 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (3)) (.branch 10 (.leaf (0)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (2))))))
  code := certificateD6_564
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 7 (.branch 3 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_565 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_565
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-9)))) (.branch 7 (.leaf (-10)) (.branch 9 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 10 (.leaf (-12)) (.leaf (-7))),
  (.branch 3 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 9 (.leaf (-7)) (.leaf (-6)))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_016_566 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2))))))
  code := certificateD6_566
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 11 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 9 (.leaf (-7)) (.leaf (-6)))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_016_567 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (3))))))
  code := certificateD6_567
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 7 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_016_568 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (2))))))
  code := certificateD6_568
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-11)) (.leaf (-10))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_569 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (3))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (1))))))
  code := certificateD6_569
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 9 (.leaf (-7)) (.leaf (-6)))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_016_570 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (4)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (5)) (.leaf (2))))))
  code := certificateD6_570
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-8)) (.leaf (-4))))),
  (.branch 10 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 14 (.leaf (-8)) (.leaf (-4)))),
  (.branch 8 (.branch 4 (.leaf (-3)) (.leaf (-2))) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 9 (.leaf (-7)) (.leaf (-6)))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_016_571 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (4))))))
  code := certificateD6_571
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_572 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (5))))))
  code := certificateD6_572
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-10)) (.leaf (-8)))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0))]
def witnessD6_016_573 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (5)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3))))))
  code := certificateD6_573
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_574 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_574
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-8)) (.leaf (-4)))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_575 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (3))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (4))) (.branch 14 (.leaf (2)) (.leaf (3))))))
  code := certificateD6_575
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_576 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2))))))
  code := certificateD6_576
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 12 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.leaf (-4)) (.branch 14 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 9 (.leaf (-7)) (.leaf (-6)))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD6_016_577 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (4))))))
  code := certificateD6_577
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-8)) (.leaf (-4))))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_578 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (4)) (.leaf (2))))))
  code := certificateD6_578
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-8)) (.leaf (-4)))),
  (.branch 3 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-2)),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-9)) (.leaf (-8))) (.branch 9 (.leaf (-7)) (.leaf (-6)))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_016_579 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (3))))))
  code := certificateD6_579
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-12))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 6 (.branch 2 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-4))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 7 (.leaf (-9)) (.branch 8 (.leaf (-8)) (.leaf (-7))))) (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_580 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (5)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2))))))
  code := certificateD6_580
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 6 (.branch 2 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 14 (.leaf (-8)) (.leaf (-4))))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-3)) (.leaf (-2))),
  (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2)))))]
def witnessD6_016_581 : CycleWitness 6 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (3))))))
  code := certificateD6_581
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 10 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 11 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 10 (.leaf (-12)) (.branch 11 (.leaf (-10)) (.leaf (-8)))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-1))]
def witnessD6_016_582 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (5))))))
  code := certificateD6_582
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 10 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD6_016_583 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1))))))
  code := certificateD6_583
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD6_016_584 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2))))))
  code := certificateD6_584
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_585 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_585
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 7 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-5))))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 7 (.leaf (-8)) (.branch 8 (.leaf (-7)) (.leaf (-6))))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_586 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (5)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (3))))))
  code := certificateD6_586
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 7 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-5))))),
  (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.leaf (-6)))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_587 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2))))))
  code := certificateD6_587
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 6 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-3)))),
  (.branch 8 (.branch 3 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 7 (.leaf (-8)) (.branch 8 (.leaf (-7)) (.leaf (-6))))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_016_588 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (4)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_588
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-7)))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 6 (.leaf (-4)) (.branch 10 (.leaf (-3)) (.leaf (-2)))),
  (.branch 8 (.leaf (-7)) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-8)) (.leaf (-7))) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_589 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (5))))))
  code := certificateD6_589
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-5)))),
  (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_590 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (4))))))
  code := certificateD6_590
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 13 (.leaf (-10)) (.leaf (-5))),
  (.branch 10 (.leaf (-3)) (.leaf (-2))),
  (.branch 12 (.branch 4 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.leaf (-6)))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_591 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.leaf (5))))))
  code := certificateD6_591
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-3)) (.leaf (-2))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_016_592 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (5)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (4))))))
  code := certificateD6_592
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 11 (.branch 6 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-6)) (.leaf (-3))))),
  (.branch 8 (.branch 3 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 4 (.leaf (-5)) (.branch 9 (.leaf (-4)) (.leaf (-3)))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016_593 : CycleWitness 6 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (4))))))
  code := certificateD6_593
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 5 (.branch 2 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5))))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 4 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_016 : Fin 65 → CycleWitness 6 := ![witnessD6_016_529, witnessD6_016_530, witnessD6_016_531, witnessD6_016_532, witnessD6_016_533, witnessD6_016_534, witnessD6_016_535, witnessD6_016_536, witnessD6_016_537, witnessD6_016_538, witnessD6_016_539, witnessD6_016_540, witnessD6_016_541, witnessD6_016_542, witnessD6_016_543, witnessD6_016_544, witnessD6_016_545, witnessD6_016_546, witnessD6_016_547, witnessD6_016_548, witnessD6_016_549, witnessD6_016_550, witnessD6_016_551, witnessD6_016_552, witnessD6_016_553, witnessD6_016_554, witnessD6_016_555, witnessD6_016_556, witnessD6_016_557, witnessD6_016_558, witnessD6_016_559, witnessD6_016_560, witnessD6_016_561, witnessD6_016_562, witnessD6_016_563, witnessD6_016_564, witnessD6_016_565, witnessD6_016_566, witnessD6_016_567, witnessD6_016_568, witnessD6_016_569, witnessD6_016_570, witnessD6_016_571, witnessD6_016_572, witnessD6_016_573, witnessD6_016_574, witnessD6_016_575, witnessD6_016_576, witnessD6_016_577, witnessD6_016_578, witnessD6_016_579, witnessD6_016_580, witnessD6_016_581, witnessD6_016_582, witnessD6_016_583, witnessD6_016_584, witnessD6_016_585, witnessD6_016_586, witnessD6_016_587, witnessD6_016_588, witnessD6_016_589, witnessD6_016_590, witnessD6_016_591, witnessD6_016_592, witnessD6_016_593]
end RealPinwheel.FiveSixths


