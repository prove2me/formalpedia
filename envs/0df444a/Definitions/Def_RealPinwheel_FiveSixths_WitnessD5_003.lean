-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD5_003
-- name    : RealPinwheel_FiveSixths_WitnessD5_003
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:05:01.386796+00:00
-- url     : https://prove2.me/theorems/d71634f7-052d-4da0-aa0c-8704dcd7d826
-- title:
--   Exact witness block D5_003
-- statement:
--   These exact witnesses represent words 148 through 216 of source certificate file D5. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D5, entries 148–216; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D5.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD5
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD5_003_147 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_147
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-5)))),
  (.leaf (0))]
  high := ![(.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 12 (.leaf (-5)) (.leaf (-4))) (.branch 14 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0))]
def witnessD5_003_148 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (1))))))
  code := certificateD5_148
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 7 (.leaf (-2)) (.branch 12 (.leaf (-1)) (.leaf (0)))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.leaf (-6)) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.branch 10 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-4)))) (.branch 13 (.leaf (-3)) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_149 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_149
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-8)) (.leaf (-4)))),
  (.branch 7 (.branch 3 (.leaf (-7)) (.leaf (-6))) (.branch 11 (.leaf (-5)) (.leaf (-4)))),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 13 (.branch 12 (.leaf (-8)) (.leaf (-6))) (.branch 14 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.leaf (-1)) (.leaf (0)))]
def witnessD5_003_150 : CycleWitness 5 where
  length := 15
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (3))))))
  code := certificateD5_150
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 13 (.leaf (-12)) (.branch 14 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-2)),
  (.branch 14 (.leaf (-2)) (.leaf (-1))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 10 (.leaf (-6)) (.leaf (-5)))) (.branch 13 (.branch 12 (.leaf (-4)) (.leaf (-3))) (.branch 14 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_151 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (4)))))
  code := certificateD5_151
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (5)) (.branch 9 (.leaf (6)) (.leaf (7)))) (.branch 12 (.leaf (8)) (.branch 13 (.leaf (9)) (.leaf (10)))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 3 (.leaf (-4)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 7 (.leaf (-8)) (.branch 8 (.leaf (-7)) (.leaf (-6))))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_152 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_152
  counts := ![(.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 10 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 12 (.leaf (7)) (.branch 13 (.leaf (8)) (.leaf (9)))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 6 (.leaf (-11)) (.leaf (-9))),
  (.branch 12 (.branch 4 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-8)) (.leaf (-7))) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_153 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_153
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 3 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))),
  (.branch 13 (.leaf (-3)) (.leaf (-2))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.leaf (-6)))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0)),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_154 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 11 (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (0)))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_154
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 10 (.leaf (-6)) (.branch 12 (.leaf (-5)) (.leaf (-4)))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_155 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 5 (.leaf (1)) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (1))))))
  code := certificateD5_155
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 8 (.branch 5 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 6 (.leaf (-9)) (.branch 7 (.leaf (-8)) (.leaf (-7))))) (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_156 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (2))))))
  code := certificateD5_156
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 13 (.leaf (-6)) (.leaf (-3))),
  (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 5 (.leaf (-2)) (.branch 10 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-8)) (.leaf (-7))) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_157 : CycleWitness 5 where
  length := 14
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (4))))))
  code := certificateD5_157
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 11 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 7 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-5))))),
  (.branch 12 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-3)))),
  (.branch 9 (.leaf (-4)) (.leaf (-3))),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_158 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_158
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 11 (.leaf (-5)) (.leaf (-3))),
  (.branch 12 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 13 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 5 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_159 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (4)) (.leaf (0))) (.branch 13 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_159
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 8 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 7 (.branch 4 (.leaf (-13)) (.leaf (-12))) (.branch 10 (.leaf (-11)) (.branch 13 (.leaf (-10)) (.leaf (-5))))),
  (.branch 11 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 9 (.branch 6 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 7 (.leaf (-8)) (.branch 8 (.leaf (-7)) (.leaf (-6))))) (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_160 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_160
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 5 (.branch 2 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5))))),
  (.branch 13 (.leaf (-4)) (.leaf (-2))),
  (.branch 12 (.leaf (-4)) (.branch 13 (.leaf (-3)) (.leaf (-2)))),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_161 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (4))))))
  code := certificateD5_161
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 13 (.leaf (-4)) (.leaf (-2))),
  (.leaf (-2)),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_162 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_162
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 5 (.branch 2 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5))))),
  (.branch 13 (.leaf (-4)) (.leaf (-2))),
  (.branch 12 (.branch 4 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-5)) (.leaf (-4)))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_163 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (4))))))
  code := certificateD5_163
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0))]
  high := ![(.branch 10 (.branch 7 (.leaf (-12)) (.leaf (-11))) (.branch 13 (.leaf (-10)) (.leaf (-5)))),
  (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0))]
def witnessD5_003_164 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (4)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.leaf (2))))))
  code := certificateD5_164
  counts := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 5 (.branch 2 (.leaf (-9)) (.leaf (-8))) (.branch 8 (.leaf (-7)) (.branch 11 (.leaf (-6)) (.leaf (-5))))),
  (.branch 12 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.leaf (-2)) (.branch 10 (.leaf (-1)) (.leaf (0)))),
  (.branch 13 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.branch 10 (.leaf (-5)) (.leaf (-4))) (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_165 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (2)) (.leaf (1))))))
  code := certificateD5_165
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 2 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.branch 3 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.leaf (0)))),
  (.branch 4 (.leaf (-5)) (.branch 9 (.leaf (-4)) (.leaf (-3)))),
  (.branch 12 (.leaf (-3)) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.branch 10 (.branch 8 (.leaf (-7)) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_166 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (2))) (.branch 13 (.leaf (3)) (.leaf (4))))))
  code := certificateD5_166
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-11)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0))]
  high := ![(.branch 11 (.branch 6 (.leaf (-13)) (.leaf (-12))) (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 13 (.leaf (-6)) (.leaf (-3))),
  (.leaf (-3)),
  (.leaf (0))]
def witnessD5_003_167 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (3)) (.leaf (2))))))
  code := certificateD5_167
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 12 (.leaf (-6)) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.branch 3 (.leaf (-8)) (.leaf (-7))) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 10 (.branch 8 (.branch 7 (.leaf (-8)) (.leaf (-7))) (.branch 9 (.leaf (-6)) (.leaf (-5)))) (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_168 : CycleWitness 5 where
  length := 14
  word := (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (4)) (.leaf (2))))))
  code := certificateD5_168
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 9 (.leaf (-5)) (.branch 13 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.leaf (-9)) (.branch 13 (.leaf (-6)) (.leaf (-3)))),
  (.branch 5 (.leaf (-2)) (.branch 10 (.leaf (-1)) (.leaf (0)))),
  (.branch 12 (.branch 11 (.leaf (-4)) (.leaf (-3))) (.branch 13 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1))]
def witnessD5_003_169 : CycleWitness 5 where
  length := 13
  word := (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 11 (.leaf (2)) (.branch 12 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_169
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 7 (.branch 3 (.leaf (-12)) (.branch 5 (.leaf (-11)) (.leaf (-10)))) (.branch 9 (.leaf (-9)) (.branch 11 (.leaf (-8)) (.leaf (-7))))),
  (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 12 (.leaf (-4)) (.leaf (-2))),
  (.branch 10 (.branch 8 (.leaf (-6)) (.branch 9 (.leaf (-5)) (.leaf (-4)))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_170 : CycleWitness 5 where
  length := 13
  word := (.branch 7 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 5 (.leaf (2)) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))) (.branch 11 (.leaf (0)) (.branch 12 (.leaf (4)) (.leaf (1))))))
  code := certificateD5_170
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 4 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 5 (.leaf (-11)) (.branch 12 (.leaf (-10)) (.leaf (-6)))),
  (.branch 7 (.leaf (-2)) (.leaf (0))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD5_003_171 : CycleWitness 5 where
  length := 13
  word := (.branch 7 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (1)) (.branch 12 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_171
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 12 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.branch 3 (.leaf (-10)) (.branch 8 (.leaf (-9)) (.leaf (-8)))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_172 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1))))))
  code := certificateD5_172
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-2)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-8))),
  (.branch 12 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 9 (.leaf (-12)) (.branch 12 (.leaf (-10)) (.leaf (-5)))),
  (.branch 8 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (0)))),
  (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-7))) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD5_003_173 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_173
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-8)))) (.branch 7 (.leaf (-9)) (.branch 9 (.leaf (-10)) (.leaf (-11))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 10 (.leaf (-11)) (.leaf (-6))),
  (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 5 (.leaf (-5)) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_174 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_174
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-8)) (.branch 7 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 8 (.leaf (-10)) (.leaf (-6))),
  (.branch 10 (.branch 3 (.leaf (-9)) (.leaf (-8))) (.branch 11 (.leaf (-6)) (.branch 12 (.leaf (-4)) (.leaf (-2))))),
  (.branch 5 (.leaf (-5)) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_175 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (2))))))
  code := certificateD5_175
  counts := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 11 (.branch 4 (.leaf (-11)) (.leaf (-10))) (.branch 12 (.leaf (-7)) (.leaf (-4)))),
  (.branch 7 (.leaf (-8)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.branch 6 (.leaf (-3)) (.leaf (-2))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_176 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (1)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_176
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 8 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 9 (.leaf (-12)) (.branch 12 (.leaf (-10)) (.leaf (-5)))),
  (.branch 6 (.leaf (-6)) (.leaf (-4))),
  (.leaf (0)),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-9)) (.leaf (-8))) (.branch 7 (.leaf (-7)) (.leaf (-6)))) (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_177 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (3))))))
  code := certificateD5_177
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 8 (.leaf (-11)) (.branch 12 (.leaf (-8)) (.leaf (-4)))),
  (.branch 9 (.leaf (-7)) (.leaf (-4))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_178 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (4))))))
  code := certificateD5_178
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-8)) (.leaf (-4)))),
  (.branch 12 (.leaf (-7)) (.leaf (-4))),
  (.branch 4 (.leaf (-4)) (.leaf (-3))),
  (.branch 9 (.branch 7 (.leaf (-7)) (.branch 8 (.leaf (-6)) (.leaf (-5)))) (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_179 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_179
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 7 (.leaf (-9)) (.branch 10 (.leaf (-7)) (.leaf (-5)))),
  (.branch 3 (.leaf (-7)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 11 (.branch 4 (.leaf (-7)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 6 (.leaf (-2)) (.branch 7 (.leaf (-1)) (.leaf (0)))),
  (.branch 10 (.branch 9 (.leaf (-5)) (.leaf (-4))) (.branch 11 (.leaf (-3)) (.branch 12 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_180 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (2))))))
  code := certificateD5_180
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 7 (.leaf (-10)) (.branch 10 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 11 (.leaf (-12)) (.branch 12 (.leaf (-8)) (.leaf (-4)))),
  (.branch 7 (.leaf (-8)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 4 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (0)))),
  (.branch 6 (.leaf (-3)) (.leaf (-2))),
  (.branch 11 (.branch 10 (.leaf (-4)) (.leaf (-3))) (.branch 12 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_181 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (2)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (3))))))
  code := certificateD5_181
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 10 (.leaf (-8)) (.leaf (-9)))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 5 (.leaf (-10)) (.branch 12 (.leaf (-8)) (.leaf (-4)))),
  (.branch 11 (.leaf (-9)) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 6 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 11 (.branch 10 (.leaf (-8)) (.leaf (-6))) (.branch 12 (.leaf (-4)) (.leaf (-2))))]
def witnessD5_003_182 : CycleWitness 5 where
  length := 13
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 7 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 11 (.leaf (3)) (.branch 12 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_182
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-7)) (.leaf (-15)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 11 (.branch 6 (.leaf (-11)) (.leaf (-9))) (.branch 12 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.leaf (-5)) (.leaf (-3))),
  (.branch 11 (.branch 10 (.leaf (-15)) (.leaf (-13))) (.branch 12 (.leaf (-11)) (.leaf (-9)))),
  (.branch 5 (.leaf (-5)) (.branch 12 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-1)) (.leaf (0)))]
def witnessD5_003_183 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (0)) (.leaf (2)))) (.branch 9 (.branch 8 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (4)))))
  code := certificateD5_183
  counts := ![(.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 8 (.branch 7 (.leaf (4)) (.leaf (5))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.leaf (0))]
  high := ![(.leaf (-2)),
  (.branch 7 (.branch 5 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 6 (.leaf (-7)) (.leaf (-6)))) (.branch 9 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 9 (.branch 7 (.leaf (-6)) (.branch 8 (.leaf (-5)) (.leaf (-4)))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_003_184 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_184
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-3)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 9 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 3 (.leaf (-6)) (.branch 11 (.leaf (-5)) (.leaf (-3)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 7 (.leaf (-6)) (.leaf (-5)))) (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_185 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (0)) (.leaf (1))))))
  code := certificateD5_185
  counts := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.leaf (7))))),
  (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 3 (.leaf (-10)) (.branch 10 (.leaf (-9)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 7 (.branch 5 (.branch 4 (.leaf (-9)) (.leaf (-8))) (.branch 6 (.leaf (-7)) (.leaf (-6)))) (.branch 9 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.branch 6 (.leaf (-7)) (.branch 7 (.leaf (-6)) (.leaf (-5)))) (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_186 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (0)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_186
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 6 (.leaf (-11)) (.branch 11 (.leaf (-10)) (.leaf (-5)))),
  (.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 7 (.leaf (-6)) (.branch 8 (.leaf (-5)) (.leaf (-4)))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_187 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (3)) (.leaf (0)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_187
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 11 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.branch 6 (.branch 5 (.leaf (-8)) (.leaf (-7))) (.branch 7 (.leaf (-6)) (.leaf (-5)))) (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_003_188 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (4)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_188
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-5))),
  (.branch 9 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 6 (.leaf (-11)) (.branch 11 (.leaf (-10)) (.leaf (-5)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 6 (.branch 5 (.leaf (-3)) (.leaf (-2))) (.branch 7 (.leaf (-1)) (.leaf (0)))),
  (.branch 9 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_189 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_189
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 9 (.branch 7 (.leaf (-6)) (.branch 8 (.leaf (-5)) (.leaf (-4)))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_190 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (1)))) (.branch 10 (.leaf (0)) (.branch 11 (.leaf (2)) (.leaf (4))))))
  code := certificateD5_190
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 9 (.branch 7 (.leaf (-6)) (.branch 8 (.leaf (-5)) (.leaf (-4)))) (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_191 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))) (.branch 10 (.leaf (1)) (.branch 11 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_191
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_192 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (4)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))) (.branch 10 (.leaf (2)) (.branch 11 (.leaf (0)) (.leaf (3))))))
  code := certificateD5_192
  counts := ![(.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 2 (.leaf (-7)) (.branch 7 (.leaf (-6)) (.leaf (-5)))),
  (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 4 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 8 (.branch 6 (.leaf (-7)) (.branch 7 (.leaf (-6)) (.leaf (-5)))) (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_193 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (2)) (.branch 8 (.leaf (4)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_193
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.leaf (-1)) (.leaf (0))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_194 : CycleWitness 5 where
  length := 12
  word := (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (0)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))) (.branch 10 (.leaf (3)) (.branch 11 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_194
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0))]
  high := ![(.branch 10 (.leaf (-3)) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 10 (.branch 9 (.leaf (-4)) (.leaf (-3))) (.branch 11 (.leaf (-2)) (.leaf (-1)))),
  (.branch 11 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0))]
def witnessD5_003_195 : CycleWitness 5 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_195
  counts := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-3)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 7 (.branch 4 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-8)) (.leaf (-4)))),
  (.branch 5 (.leaf (-6)) (.branch 8 (.leaf (-5)) (.leaf (-4)))),
  (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1)))),
  (.branch 8 (.branch 6 (.leaf (-6)) (.branch 7 (.leaf (-5)) (.leaf (-4)))) (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_196 : CycleWitness 5 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (1)) (.branch 7 (.leaf (0)) (.leaf (3)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_196
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 7 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-6)) (.leaf (-7)))) (.branch 7 (.leaf (-8)) (.branch 9 (.leaf (-9)) (.leaf (-10))))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.leaf (0))]
  high := ![(.branch 10 (.leaf (-10)) (.leaf (-5))),
  (.branch 3 (.leaf (-5)) (.branch 7 (.leaf (-4)) (.leaf (-3)))),
  (.branch 7 (.branch 5 (.leaf (-7)) (.branch 6 (.leaf (-6)) (.leaf (-5)))) (.branch 9 (.branch 8 (.leaf (-4)) (.leaf (-3))) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_003_197 : CycleWitness 5 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (2)) (.leaf (0))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (2)) (.branch 10 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_197
  counts := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 6 (.leaf (-8)) (.leaf (-5))),
  (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-6))) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.branch 10 (.leaf (-4)) (.leaf (-2))),
  (.branch 8 (.branch 7 (.leaf (-5)) (.leaf (-4))) (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_198 : CycleWitness 5 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_198
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 5 (.branch 2 (.leaf (-7)) (.leaf (-6))) (.branch 8 (.leaf (-5)) (.leaf (-4)))),
  (.branch 6 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.branch 8 (.branch 7 (.leaf (-5)) (.leaf (-4))) (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_199 : CycleWitness 5 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (2)) (.leaf (0)))) (.branch 9 (.leaf (1)) (.branch 10 (.leaf (2)) (.leaf (4))))))
  code := certificateD5_199
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 11 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 9 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-6)) (.leaf (-3)))),
  (.branch 6 (.leaf (-7)) (.branch 10 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 8 (.branch 7 (.leaf (-5)) (.leaf (-4))) (.branch 9 (.leaf (-3)) (.branch 10 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_200 : CycleWitness 5 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 8 (.branch 6 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (0)) (.branch 10 (.leaf (4)) (.leaf (3))))))
  code := certificateD5_200
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 7 (.leaf (-9)) (.branch 10 (.leaf (-8)) (.leaf (-4)))),
  (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-6))) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.branch 9 (.leaf (-6)) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.branch 6 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1))]
def witnessD5_003_201 : CycleWitness 5 where
  length := 11
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 8 (.branch 6 (.leaf (3)) (.branch 7 (.leaf (1)) (.leaf (0)))) (.branch 9 (.leaf (4)) (.branch 10 (.leaf (2)) (.leaf (3))))))
  code := certificateD5_201
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-8)) (.leaf (-10)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 9 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 10 (.leaf (-6)) (.leaf (-3)))),
  (.branch 9 (.branch 8 (.leaf (-8)) (.leaf (-6))) (.branch 10 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.leaf (0)),
  (.branch 4 (.leaf (-5)) (.branch 10 (.leaf (-4)) (.leaf (-2))))]
def witnessD5_003_202 : CycleWitness 5 where
  length := 10
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (3))))))
  code := certificateD5_202
  counts := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 9 (.leaf (-4)) (.leaf (-2))),
  (.branch 6 (.leaf (-5)) (.leaf (-3))),
  (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 7 (.branch 5 (.leaf (-6)) (.branch 6 (.leaf (-5)) (.leaf (-4)))) (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1)))))]
def witnessD5_003_203 : CycleWitness 5 where
  length := 10
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_203
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 10 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 7 (.leaf (-8)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.leaf (0))]
  high := ![(.branch 8 (.leaf (-9)) (.branch 9 (.leaf (-6)) (.leaf (-3)))),
  (.branch 3 (.leaf (-4)) (.leaf (-3))),
  (.branch 9 (.leaf (-2)) (.leaf (-1))),
  (.branch 7 (.branch 6 (.leaf (-5)) (.leaf (-4))) (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD5_003_204 : CycleWitness 5 where
  length := 10
  word := (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.branch 4 (.leaf (0)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (2))))))
  code := certificateD5_204
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 5 (.leaf (-8)) (.branch 9 (.leaf (-6)) (.leaf (-3)))),
  (.branch 8 (.leaf (-3)) (.branch 9 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 4 (.leaf (-2)) (.leaf (-1))),
  (.branch 8 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 9 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_205 : CycleWitness 5 where
  length := 9
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4))))))
  code := certificateD5_205
  counts := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 8 (.leaf (3)) (.leaf (4))))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 4 (.leaf (-6)) (.leaf (-4))),
  (.branch 3 (.leaf (-5)) (.branch 8 (.leaf (-4)) (.leaf (-2)))),
  (.branch 6 (.branch 5 (.leaf (-5)) (.leaf (-4))) (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1))))),
  (.branch 7 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 8 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_003_206 : CycleWitness 5 where
  length := 9
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (4))))))
  code := certificateD5_206
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0))]
  high := ![(.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 6 (.branch 4 (.leaf (-6)) (.branch 5 (.leaf (-5)) (.leaf (-4)))) (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1))))),
  (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_003_207 : CycleWitness 5 where
  length := 9
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (4))))))
  code := certificateD5_207
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 9 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 8 (.leaf (-2)) (.leaf (-1))),
  (.branch 7 (.leaf (-6)) (.branch 8 (.leaf (-4)) (.leaf (-2)))),
  (.branch 4 (.leaf (-3)) (.leaf (-2))),
  (.branch 7 (.branch 6 (.leaf (-4)) (.leaf (-3))) (.branch 8 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_003_208 : CycleWitness 5 where
  length := 9
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (2))))))
  code := certificateD5_208
  counts := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 7 (.branch 6 (.leaf (-8)) (.leaf (-6))) (.branch 8 (.leaf (-4)) (.leaf (-2)))),
  (.branch 4 (.leaf (-3)) (.leaf (-2))),
  (.branch 5 (.leaf (-1)) (.leaf (0))),
  (.branch 3 (.leaf (-5)) (.branch 8 (.leaf (-4)) (.leaf (-2)))),
  (.branch 7 (.leaf (-3)) (.branch 8 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_209 : CycleWitness 5 where
  length := 8
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4)))))
  code := certificateD5_209
  counts := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.branch 7 (.leaf (3)) (.leaf (4))))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-2))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 5 (.branch 3 (.leaf (-6)) (.branch 4 (.leaf (-5)) (.leaf (-4)))) (.branch 6 (.leaf (-3)) (.branch 7 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 7 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0))]
def witnessD5_003_210 : CycleWitness 5 where
  length := 8
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4)))))
  code := certificateD5_210
  counts := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.leaf (0))]
  high := ![(.branch 2 (.leaf (-5)) (.branch 5 (.leaf (-4)) (.leaf (-3)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.branch 5 (.branch 4 (.leaf (-5)) (.leaf (-4))) (.branch 6 (.leaf (-3)) (.branch 7 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.leaf (-3)) (.branch 7 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_003_211 : CycleWitness 5 where
  length := 8
  word := (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (4)))))
  code := certificateD5_211
  counts := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 8 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-3))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 6 (.leaf (-3)) (.branch 7 (.leaf (-2)) (.leaf (-1)))),
  (.branch 7 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 6 (.branch 5 (.leaf (-4)) (.leaf (-3))) (.branch 7 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_003_212 : CycleWitness 5 where
  length := 7
  word := (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (3)))))
  code := certificateD5_212
  counts := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 4 (.leaf (-5)) (.leaf (-3))),
  (.branch 4 (.branch 3 (.leaf (-5)) (.leaf (-4))) (.branch 5 (.leaf (-3)) (.branch 6 (.leaf (-2)) (.leaf (-1))))),
  (.branch 6 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 5 (.leaf (-3)) (.branch 6 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003_213 : CycleWitness 5 where
  length := 7
  word := (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4)))))
  code := certificateD5_213
  counts := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 7 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.leaf (0))]
  high := ![(.branch 5 (.leaf (-6)) (.branch 6 (.leaf (-4)) (.leaf (-2)))),
  (.branch 3 (.leaf (-3)) (.leaf (-2))),
  (.branch 6 (.leaf (-2)) (.leaf (-1))),
  (.branch 5 (.branch 4 (.leaf (-4)) (.leaf (-3))) (.branch 6 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD5_003_214 : CycleWitness 5 where
  length := 6
  word := (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4)))))
  code := certificateD5_214
  counts := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))),
  (.branch 2 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.leaf (0))]
  high := ![(.branch 5 (.leaf (-2)) (.leaf (-1))),
  (.branch 4 (.branch 3 (.leaf (-4)) (.leaf (-3))) (.branch 5 (.leaf (-2)) (.leaf (-1)))),
  (.branch 4 (.leaf (-3)) (.branch 5 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0))]
def witnessD5_003_215 : CycleWitness 5 where
  length := 5
  word := (.branch 2 (.branch 1 (.leaf (0)) (.leaf (4))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (2)) (.leaf (3)))))
  code := certificateD5_215
  counts := ![(.branch 1 (.leaf (0)) (.leaf (1))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 2 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 3 (.branch 2 (.leaf (-4)) (.leaf (-3))) (.branch 4 (.leaf (-2)) (.leaf (-1)))),
  (.branch 4 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 3 (.leaf (-3)) (.branch 4 (.leaf (-2)) (.leaf (-1))))]
def witnessD5_003 : Fin 69 → CycleWitness 5 := ![witnessD5_003_147, witnessD5_003_148, witnessD5_003_149, witnessD5_003_150, witnessD5_003_151, witnessD5_003_152, witnessD5_003_153, witnessD5_003_154, witnessD5_003_155, witnessD5_003_156, witnessD5_003_157, witnessD5_003_158, witnessD5_003_159, witnessD5_003_160, witnessD5_003_161, witnessD5_003_162, witnessD5_003_163, witnessD5_003_164, witnessD5_003_165, witnessD5_003_166, witnessD5_003_167, witnessD5_003_168, witnessD5_003_169, witnessD5_003_170, witnessD5_003_171, witnessD5_003_172, witnessD5_003_173, witnessD5_003_174, witnessD5_003_175, witnessD5_003_176, witnessD5_003_177, witnessD5_003_178, witnessD5_003_179, witnessD5_003_180, witnessD5_003_181, witnessD5_003_182, witnessD5_003_183, witnessD5_003_184, witnessD5_003_185, witnessD5_003_186, witnessD5_003_187, witnessD5_003_188, witnessD5_003_189, witnessD5_003_190, witnessD5_003_191, witnessD5_003_192, witnessD5_003_193, witnessD5_003_194, witnessD5_003_195, witnessD5_003_196, witnessD5_003_197, witnessD5_003_198, witnessD5_003_199, witnessD5_003_200, witnessD5_003_201, witnessD5_003_202, witnessD5_003_203, witnessD5_003_204, witnessD5_003_205, witnessD5_003_206, witnessD5_003_207, witnessD5_003_208, witnessD5_003_209, witnessD5_003_210, witnessD5_003_211, witnessD5_003_212, witnessD5_003_213, witnessD5_003_214, witnessD5_003_215]
end RealPinwheel.FiveSixths


