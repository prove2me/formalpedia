-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD5_002
-- name    : RealPinwheel_FiveSixths_WitnessD5_002
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:00:49.848411+00:00
-- url     : https://prove2.me/theorems/be0afa05-5ca4-403c-95bb-fdfa390654c0
-- title:
--   Exact witness block D5_002
-- statement:
--   These exact witnesses represent words 87 through 147 of source certificate file D5. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D5, entries 87–147; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D5.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD5
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD5_002_86 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_86
  counts := ![(.branch 9 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 18 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 16 (.leaf (-10)) (.branch 17 (.leaf (-7)) (.leaf (-4)))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.branch 15 (.leaf (-4)) (.leaf (0))))),
  (.branch 4 (.leaf (-3)) (.leaf (-2))),
  (.branch 17 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-11)) (.leaf (-10))) (.branch 10 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))) (.branch 15 (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_002_87 : CycleWitness 5 where
  length := 18
  word := (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_87
  counts := ![(.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 11 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 8 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 12 (.leaf (-13)) (.branch 15 (.leaf (-10)) (.leaf (-7)))),
  (.branch 3 (.leaf (-5)) (.branch 17 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 15 (.branch 4 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))),
  (.branch 13 (.branch 10 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 11 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-6))))) (.branch 15 (.branch 14 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.branch 17 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_002_88 : CycleWitness 5 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.leaf (4)))))
  code := certificateD5_88
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (6))))) (.branch 12 (.branch 10 (.leaf (7)) (.branch 11 (.leaf (8)) (.leaf (9)))) (.branch 15 (.branch 14 (.leaf (10)) (.leaf (11))) (.branch 16 (.leaf (12)) (.leaf (13)))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 3 (.leaf (-8)) (.branch 4 (.leaf (-12)) (.leaf (-16))))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 9 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 9 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 13 (.leaf (-14)) (.leaf (-13)))),
  (.branch 11 (.branch 8 (.branch 6 (.leaf (-12)) (.branch 7 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-7))))) (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_002_89 : CycleWitness 5 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_89
  counts := ![(.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 12 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 14 (.leaf (7)) (.branch 16 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 9 (.branch 5 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 7 (.leaf (-14)) (.leaf (-13)))) (.branch 13 (.branch 11 (.leaf (-12)) (.leaf (-11))) (.branch 15 (.leaf (-10)) (.leaf (-9))))),
  (.branch 10 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.leaf (-2)) (.branch 9 (.leaf (-1)) (.leaf (0)))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_90 : CycleWitness 5 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_90
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 4 (.leaf (-12)) (.branch 6 (.leaf (-13)) (.leaf (-14))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 7 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-8)))),
  (.branch 4 (.leaf (-5)) (.leaf (-4))),
  (.branch 11 (.leaf (-2)) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_91 : CycleWitness 5 where
  length := 17
  word := (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_91
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 13 (.branch 9 (.leaf (5)) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.leaf (8)) (.branch 16 (.leaf (9)) (.leaf (10)))))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 8 (.leaf (-15)) (.branch 15 (.leaf (-13)) (.leaf (-10)))),
  (.branch 14 (.branch 4 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-8)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 6 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_92 : CycleWitness 5 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_92
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 15 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-5)),
  (.branch 13 (.leaf (-3)) (.leaf (0))),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 16 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_002_93 : CycleWitness 5 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (3)) (.leaf (1))))))
  code := certificateD5_93
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 15 (.leaf (-4)) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 7 (.leaf (-4)) (.branch 14 (.leaf (-3)) (.leaf (0)))),
  (.branch 10 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_94 : CycleWitness 5 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.leaf (1))))))
  code := certificateD5_94
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 14 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 3 (.leaf (-16)) (.branch 16 (.leaf (-15)) (.leaf (-8)))),
  (.branch 7 (.leaf (-2)) (.branch 11 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-2)),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-13)) (.branch 6 (.leaf (-12)) (.leaf (-11)))) (.branch 8 (.leaf (-10)) (.branch 9 (.leaf (-9)) (.leaf (-8))))) (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_95 : CycleWitness 5 where
  length := 17
  word := (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_95
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 8 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 4 (.leaf (-5)) (.leaf (-4))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.branch 5 (.leaf (-5)) (.leaf (-4))) (.branch 16 (.leaf (-3)) (.leaf (-2)))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_96 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))))))
  code := certificateD5_96
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 5 (.leaf (-13)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-16)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 11 (.branch 6 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-14)) (.leaf (-7)))),
  (.branch 10 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.branch 16 (.leaf (-11)) (.leaf (-8))))),
  (.leaf (0)),
  (.branch 8 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_97 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3)))))))
  code := certificateD5_97
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-16)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 10 (.branch 4 (.leaf (-16)) (.branch 7 (.leaf (-15)) (.leaf (-14)))) (.branch 13 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-2)),
  (.branch 15 (.branch 14 (.leaf (-8)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_98 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (3)))))))
  code := certificateD5_98
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 11 (.branch 9 (.leaf (-12)) (.leaf (-13))) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 14 (.leaf (-15)) (.leaf (-8))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 14 (.branch 13 (.leaf (-10)) (.leaf (-8))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-4)) (.leaf (-2))))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_002_99 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_99
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.branch 16 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 9 (.branch 7 (.leaf (-11)) (.leaf (-12))) (.branch 11 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 12 (.leaf (-14)) (.leaf (-8))),
  (.branch 15 (.branch 14 (.leaf (-12)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.leaf (-2)) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 7 (.leaf (-5)) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_100 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3)))))))
  code := certificateD5_100
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 9 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-7)))),
  (.branch 15 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-7)) (.leaf (-4)))),
  (.branch 10 (.leaf (-7)) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 12 (.branch 9 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.branch 11 (.leaf (-7)) (.leaf (-6))))) (.branch 14 (.branch 13 (.leaf (-5)) (.leaf (-4))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_002_101 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (4))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2)))))))
  code := certificateD5_101
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-10)) (.leaf (-13)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 15 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-6)) (.leaf (-10)))),
  (.branch 14 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 9 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 14 (.leaf (-11)) (.leaf (-7)))),
  (.branch 16 (.leaf (-10)) (.leaf (-5))),
  (.branch 8 (.leaf (-2)) (.branch 9 (.leaf (-1)) (.leaf (0)))),
  (.branch 13 (.branch 11 (.leaf (-10)) (.branch 12 (.leaf (-9)) (.leaf (-8)))) (.branch 15 (.branch 14 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-5)) (.leaf (-4))))),
  (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_102 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (3)))))))
  code := certificateD5_102
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 8 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 15 (.branch 8 (.leaf (-16)) (.leaf (-15))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 9 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 10 (.branch 4 (.leaf (-8)) (.leaf (-7))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.leaf (-2)) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_103 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (1)))))))
  code := certificateD5_103
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 13 (.leaf (-13)) (.branch 16 (.leaf (-12)) (.leaf (-6)))),
  (.branch 10 (.branch 6 (.leaf (-7)) (.leaf (-6))) (.branch 14 (.leaf (-5)) (.branch 15 (.leaf (-2)) (.leaf (0))))),
  (.branch 15 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 7 (.leaf (-3)) (.leaf (-2))),
  (.branch 14 (.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-5)) (.leaf (-4)))) (.branch 15 (.leaf (-3)) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_104 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3)))))))
  code := certificateD5_104
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 12 (.branch 8 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-5)) (.leaf (-3)))),
  (.branch 15 (.branch 6 (.leaf (-11)) (.leaf (-10))) (.branch 16 (.leaf (-7)) (.leaf (-4)))),
  (.leaf (-4)),
  (.leaf (0)),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_105 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4)))))))
  code := certificateD5_105
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-14)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.branch 16 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-5)) (.leaf (-9)))),
  (.leaf (0))]
  high := ![(.branch 13 (.branch 10 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-12)) (.leaf (-6)))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-4)),
  (.branch 14 (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-8)) (.leaf (-7)))) (.branch 15 (.leaf (-6)) (.branch 16 (.leaf (-5)) (.leaf (-4))))),
  (.leaf (0))]
def witnessD5_002_106 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3)))))))
  code := certificateD5_106
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 8 (.branch 2 (.leaf (-11)) (.branch 5 (.leaf (-10)) (.leaf (-9)))) (.branch 11 (.leaf (-8)) (.branch 14 (.leaf (-7)) (.leaf (-6))))),
  (.branch 7 (.leaf (-10)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 16 (.leaf (-6)) (.leaf (-3)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-7))) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_107 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (1)))))))
  code := certificateD5_107
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 17 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 12 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 16 (.leaf (-10)) (.leaf (-5)))),
  (.branch 10 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (0)))),
  (.branch 8 (.leaf (-6)) (.leaf (-4))),
  (.branch 15 (.branch 6 (.leaf (-7)) (.leaf (-6))) (.branch 16 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.branch 11 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-5)))) (.branch 15 (.branch 14 (.leaf (-4)) (.leaf (-3))) (.branch 16 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_108 : CycleWitness 5 where
  length := 17
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4)))))))
  code := certificateD5_108
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 11 (.leaf (-6)) (.branch 15 (.leaf (-7)) (.leaf (-8))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.branch 16 (.leaf (-3)) (.leaf (-4))))),
  (.leaf (0))]
  high := ![(.branch 15 (.branch 14 (.leaf (-16)) (.leaf (-12))) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.leaf (-12)) (.branch 16 (.leaf (-8)) (.leaf (-4)))),
  (.branch 16 (.leaf (-8)) (.leaf (-4))),
  (.leaf (-4)),
  (.leaf (0))]
def witnessD5_002_109 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (4)))))
  code := certificateD5_109
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 11 (.branch 9 (.leaf (6)) (.branch 10 (.leaf (7)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (9)) (.leaf (10))) (.branch 15 (.leaf (11)) (.leaf (12)))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.leaf (-3)),
  (.branch 10 (.branch 7 (.branch 5 (.leaf (-12)) (.branch 6 (.leaf (-11)) (.leaf (-10)))) (.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-8)) (.leaf (-7))))) (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_002_110 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (1))))))
  code := certificateD5_110
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 4 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 10 (.branch 5 (.leaf (-16)) (.leaf (-15))) (.branch 15 (.leaf (-14)) (.leaf (-9)))),
  (.branch 14 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD5_002_111 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_111
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_112 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2))))))
  code := certificateD5_112
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD5_002_113 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (1))))))
  code := certificateD5_113
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-9)) (.leaf (-18)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 9 (.branch 3 (.leaf (-18)) (.branch 6 (.leaf (-17)) (.leaf (-16)))) (.branch 12 (.leaf (-15)) (.branch 15 (.leaf (-14)) (.leaf (-9))))),
  (.branch 13 (.leaf (-4)) (.branch 14 (.leaf (-1)) (.leaf (0)))),
  (.branch 10 (.leaf (-5)) (.leaf (-3))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_114 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2))))))
  code := certificateD5_114
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 10 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-4)))),
  (.branch 14 (.leaf (-9)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.leaf (-2)) (.leaf (0))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD5_002_115 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1))))))
  code := certificateD5_115
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 8 (.branch 3 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.leaf (-9)))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.branch 8 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 9 (.leaf (-8)) (.branch 10 (.leaf (-7)) (.leaf (-6))))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_116 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (3))))))
  code := certificateD5_116
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 10 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-4)))),
  (.branch 5 (.leaf (-4)) (.leaf (-3))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_117 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (1))))))
  code := certificateD5_117
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 10 (.leaf (-8)) (.branch 15 (.leaf (-7)) (.leaf (-4)))),
  (.branch 7 (.leaf (-2)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_118 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_118
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_002_119 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_119
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_002_120 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_120
  counts := ![(.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 4 (.leaf (-11)) (.branch 11 (.leaf (-10)) (.leaf (-7)))),
  (.branch 10 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_121 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3))))))
  code := certificateD5_121
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 12 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-5)) (.leaf (-3))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_122 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (3))))))
  code := certificateD5_122
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.leaf (-8)) (.leaf (-5))),
  (.branch 14 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_002_123 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2))))))
  code := certificateD5_123
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 12 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 3 (.leaf (-10)) (.leaf (-9))) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.leaf (-2)) (.leaf (0))),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1))]
def witnessD5_002_124 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_124
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-7)) (.leaf (-5))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_002_125 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3))))))
  code := certificateD5_125
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 7 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 8 (.leaf (-13)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_126 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_126
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 8 (.leaf (-7)) (.branch 11 (.leaf (-8)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 12 (.leaf (-9)) (.leaf (-5))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.branch 13 (.leaf (-6)) (.leaf (-5))) (.branch 15 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0))]
def witnessD5_002_127 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_127
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-7)) (.leaf (-5))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0))]
def witnessD5_002_128 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_128
  counts := ![(.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 5 (.leaf (-8)) (.branch 12 (.leaf (-7)) (.leaf (-5)))),
  (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-9)) (.leaf (-8))) (.branch 10 (.leaf (-7)) (.leaf (-6)))) (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1))))))]
def witnessD5_002_129 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3))))))
  code := certificateD5_129
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-12)))) (.branch 10 (.leaf (-13)) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-3)) (.leaf (-4))))]
  high := ![(.branch 14 (.leaf (-15)) (.branch 15 (.leaf (-10)) (.leaf (-5)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 4 (.leaf (-7)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_130 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (3)) (.leaf (2))))))
  code := certificateD5_130
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 5 (.leaf (-4)) (.leaf (-3))),
  (.branch 12 (.branch 10 (.branch 9 (.leaf (-8)) (.leaf (-7))) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_131 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.leaf (3))))))
  code := certificateD5_131
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.leaf (-8)) (.branch 15 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_132 : CycleWitness 5 where
  length := 16
  word := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_132
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 10 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 15 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 9 (.branch 6 (.branch 4 (.leaf (-13)) (.branch 5 (.leaf (-12)) (.leaf (-11)))) (.branch 7 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8))))) (.branch 12 (.branch 10 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5)))) (.branch 14 (.branch 13 (.leaf (-4)) (.leaf (-3))) (.branch 15 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.branch 15 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_133 : CycleWitness 5 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_133
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (9)))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 13 (.leaf (-4)) (.leaf (-3))),
  (.branch 12 (.branch 11 (.leaf (-10)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 11 (.branch 9 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_002_134 : CycleWitness 5 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (3))))))
  code := certificateD5_134
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 4 (.leaf (-10)) (.branch 6 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 7 (.leaf (-12)) (.branch 14 (.leaf (-11)) (.leaf (-7)))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_135 : CycleWitness 5 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (1))))))
  code := certificateD5_135
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 7 (.branch 3 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))),
  (.branch 8 (.branch 4 (.leaf (-3)) (.leaf (-2))) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 14 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_002_136 : CycleWitness 5 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (3))))))
  code := certificateD5_136
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 3 (.leaf (-14)) (.branch 14 (.leaf (-13)) (.leaf (-7)))),
  (.branch 7 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 13 (.branch 5 (.leaf (-7)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 11 (.branch 9 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_137 : CycleWitness 5 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (0)) (.leaf (1))))))
  code := certificateD5_137
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 7 (.branch 3 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.branch 14 (.leaf (-2)) (.leaf (-1)))]
def witnessD5_002_138 : CycleWitness 5 where
  length := 15
  word := (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (4)) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_138
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 7 (.branch 3 (.leaf (-14)) (.branch 5 (.leaf (-13)) (.leaf (-12)))) (.branch 11 (.branch 9 (.leaf (-11)) (.leaf (-10))) (.branch 13 (.leaf (-9)) (.leaf (-8))))),
  (.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_139 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_139
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 14 (.leaf (-4)) (.leaf (-2))),
  (.leaf (-2)),
  (.branch 10 (.branch 7 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 8 (.leaf (-8)) (.branch 9 (.leaf (-7)) (.leaf (-6))))) (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_002_140 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_140
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 12 (.leaf (-3)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-5)) (.leaf (-4)))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_002_141 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_141
  counts := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-8)) (.leaf (-9)))) (.branch 7 (.leaf (-10)) (.branch 9 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 10 (.leaf (-12)) (.leaf (-7))),
  (.branch 3 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-2)) (.branch 8 (.leaf (-1)) (.leaf (0)))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_142 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2))))))
  code := certificateD5_142
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 11 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.branch 7 (.leaf (-3)) (.leaf (-2))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_143 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (4))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_143
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 6 (.leaf (-5)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 13 (.branch 5 (.leaf (-7)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_144 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2))))))
  code := certificateD5_144
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 10 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_002_145 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (1))))))
  code := certificateD5_145
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 9 (.leaf (-1)) (.leaf (0))),
  (.branch 12 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2))))),
  (.branch 7 (.leaf (-3)) (.leaf (-2))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002_146 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (3)) (.leaf (2))))))
  code := certificateD5_146
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-14)) (.leaf (-13))) (.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-8)) (.leaf (-4))))),
  (.branch 10 (.branch 6 (.leaf (-10)) (.leaf (-9))) (.branch 14 (.leaf (-8)) (.leaf (-4)))),
  (.branch 8 (.branch 4 (.leaf (-3)) (.leaf (-2))) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 7 (.leaf (-3)) (.leaf (-2))),
  (.branch 12 (.branch 11 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_002 : Fin 61 → CycleWitness 5 := ![witnessD5_002_86, witnessD5_002_87, witnessD5_002_88, witnessD5_002_89, witnessD5_002_90, witnessD5_002_91, witnessD5_002_92, witnessD5_002_93, witnessD5_002_94, witnessD5_002_95, witnessD5_002_96, witnessD5_002_97, witnessD5_002_98, witnessD5_002_99, witnessD5_002_100, witnessD5_002_101, witnessD5_002_102, witnessD5_002_103, witnessD5_002_104, witnessD5_002_105, witnessD5_002_106, witnessD5_002_107, witnessD5_002_108, witnessD5_002_109, witnessD5_002_110, witnessD5_002_111, witnessD5_002_112, witnessD5_002_113, witnessD5_002_114, witnessD5_002_115, witnessD5_002_116, witnessD5_002_117, witnessD5_002_118, witnessD5_002_119, witnessD5_002_120, witnessD5_002_121, witnessD5_002_122, witnessD5_002_123, witnessD5_002_124, witnessD5_002_125, witnessD5_002_126, witnessD5_002_127, witnessD5_002_128, witnessD5_002_129, witnessD5_002_130, witnessD5_002_131, witnessD5_002_132, witnessD5_002_133, witnessD5_002_134, witnessD5_002_135, witnessD5_002_136, witnessD5_002_137, witnessD5_002_138, witnessD5_002_139, witnessD5_002_140, witnessD5_002_141, witnessD5_002_142, witnessD5_002_143, witnessD5_002_144, witnessD5_002_145, witnessD5_002_146]
end RealPinwheel.FiveSixths


