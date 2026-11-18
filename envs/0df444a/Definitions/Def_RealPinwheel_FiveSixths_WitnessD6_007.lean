-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_007
-- name    : RealPinwheel_FiveSixths_WitnessD6_007
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:23:31.111603+00:00
-- url     : https://prove2.me/theorems/9d319d8c-6eaf-4d14-887b-9d2fa386345f
-- title:
--   Exact witness block D6_007
-- statement:
--   These exact witnesses represent words 162 through 191 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 162–191; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_007_161 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (5)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (4)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (3))))))))
  code := certificateD6_161
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-19)) (.leaf (-20)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-9)) (.leaf (-12)))),
  (.branch 16 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 27 (.branch 24 (.leaf (-15)) (.leaf (-14))) (.branch 30 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-6))))),
  (.branch 26 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 21 (.branch 14 (.leaf (-3)) (.leaf (-2))) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))),
  (.leaf (-1))]
def witnessD6_007_162 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (5))))))))
  code := certificateD6_162
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 11 (.leaf (-6)) (.branch 15 (.leaf (-7)) (.leaf (-8))))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 12 (.leaf (-2)) (.branch 16 (.leaf (-3)) (.leaf (-4))))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.leaf (-12)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 33 (.leaf (-8)) (.leaf (-4))),
  (.leaf (-4)),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))) (.branch 23 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-10))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_007_163 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (5)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4))))))))
  code := certificateD6_163
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 18 (.leaf (-9)) (.branch 22 (.leaf (-11)) (.leaf (-12))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.branch 19 (.leaf (-6)) (.leaf (-8))))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 2 (.leaf (-20)) (.branch 33 (.leaf (-19)) (.leaf (-12)))),
  (.branch 32 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.branch 20 (.leaf (-8)) (.branch 29 (.leaf (-7)) (.leaf (-5)))),
  (.branch 31 (.branch 21 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 29 (.branch 27 (.branch 9 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_007_164 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (5))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (1)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (5))) (.branch 28 (.leaf (2)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4))))))))
  code := certificateD6_164
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-12))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 26 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 32 (.branch 21 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 31 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_007_165 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (3)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (4)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (3))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4))))))))
  code := certificateD6_165
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-14)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 33 (.leaf (-6)) (.leaf (-4))),
  (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 25 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_007_166 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (4)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (5))) (.branch 24 (.leaf (2)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (4)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (2))))))))
  code := certificateD6_166
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-6)) (.leaf (-11)))),
  (.branch 6 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 31 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 32 (.leaf (-11)) (.branch 33 (.leaf (-8)) (.leaf (-5))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.leaf (-17)))) (.branch 28 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-11)),
  (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_007_167 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (4))))))))
  code := certificateD6_167
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-19)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-8)) (.branch 29 (.leaf (-7)) (.leaf (-5)))),
  (.branch 26 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.branch 24 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.branch 28 (.leaf (-1)) (.leaf (0))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_007_168 : CycleWitness 6 where
  length := 33
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 13 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.leaf (0)))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (4)) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_168
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 28 (.branch 26 (.leaf (14)) (.leaf (15))) (.branch 30 (.leaf (16)) (.branch 32 (.leaf (17)) (.leaf (18))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-5)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-26))),
  (.branch 18 (.leaf (0)) (.leaf (-15))),
  (.branch 29 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 27 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 31 (.leaf (-7)) (.leaf (-6))))),
  (.branch 26 (.leaf (-5)) (.branch 32 (.leaf (-4)) (.leaf (-2)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.branch 13 (.branch 10 (.branch 8 (.leaf (-26)) (.branch 9 (.leaf (-25)) (.leaf (-24)))) (.branch 11 (.leaf (-23)) (.branch 12 (.leaf (-22)) (.leaf (-21))))) (.branch 16 (.branch 14 (.leaf (-20)) (.branch 15 (.leaf (-19)) (.leaf (-18)))) (.branch 18 (.branch 17 (.leaf (-17)) (.leaf (-16))) (.branch 19 (.leaf (-15)) (.leaf (-14)))))) (.branch 26 (.branch 23 (.branch 21 (.leaf (-13)) (.branch 22 (.leaf (-12)) (.leaf (-11)))) (.branch 24 (.leaf (-10)) (.branch 25 (.leaf (-9)) (.leaf (-8))))) (.branch 29 (.branch 27 (.leaf (-7)) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 21 (.branch 19 (.leaf (-15)) (.branch 20 (.leaf (-14)) (.leaf (-13)))) (.branch 23 (.branch 22 (.leaf (-12)) (.leaf (-11))) (.branch 24 (.leaf (-10)) (.leaf (-9))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-7))) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_007_169 : CycleWitness 6 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (5))) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (4)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_169
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 25 (.branch 20 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 9 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 26 (.leaf (-26)) (.leaf (-30)))),
  (.branch 13 (.branch 11 (.leaf (0)) (.leaf (-3))) (.branch 21 (.leaf (-9)) (.leaf (-13)))),
  (.branch 8 (.leaf (0)) (.branch 14 (.leaf (-2)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-29))),
  (.branch 28 (.leaf (0)) (.leaf (-5))),
  (.branch 18 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 27 (.leaf (-30)) (.branch 32 (.leaf (-29)) (.leaf (-20)))),
  (.branch 28 (.branch 22 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 31 (.leaf (-10)) (.branch 32 (.leaf (-3)) (.leaf (0))))),
  (.branch 15 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8)))),
  (.branch 18 (.branch 11 (.branch 7 (.branch 5 (.leaf (-29)) (.branch 6 (.leaf (-28)) (.leaf (-27)))) (.branch 9 (.branch 8 (.leaf (-26)) (.leaf (-25))) (.branch 10 (.leaf (-24)) (.leaf (-23))))) (.branch 14 (.branch 12 (.leaf (-22)) (.branch 13 (.leaf (-21)) (.leaf (-20)))) (.branch 16 (.branch 15 (.leaf (-19)) (.leaf (-18))) (.branch 17 (.leaf (-17)) (.leaf (-16)))))) (.branch 25 (.branch 21 (.branch 19 (.leaf (-15)) (.branch 20 (.leaf (-14)) (.leaf (-13)))) (.branch 23 (.branch 22 (.leaf (-12)) (.leaf (-11))) (.branch 24 (.leaf (-10)) (.leaf (-9))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-7))) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 29 (.leaf (-5)) (.leaf (-4))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 21 (.branch 19 (.leaf (-15)) (.branch 20 (.leaf (-14)) (.leaf (-13)))) (.branch 23 (.branch 22 (.leaf (-12)) (.leaf (-11))) (.branch 24 (.leaf (-10)) (.leaf (-9))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-7))) (.branch 28 (.leaf (-6)) (.leaf (-5)))) (.branch 31 (.branch 30 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_007_170 : CycleWitness 6 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (0))) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (4)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (0)) (.leaf (5))))))))
  code := certificateD6_170
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-5)) (.leaf (-7)))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 19 (.leaf (-22)) (.leaf (-23)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-9))) (.branch 22 (.leaf (-10)) (.branch 30 (.leaf (-11)) (.leaf (-12))))),
  (.branch 8 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 27 (.branch 24 (.leaf (-7)) (.leaf (-6))) (.branch 30 (.leaf (-5)) (.leaf (-4)))),
  (.branch 28 (.leaf (-7)) (.branch 32 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 20 (.leaf (-23)) (.branch 29 (.leaf (-20)) (.leaf (-16)))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-8)) (.leaf (-4))))),
  (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-8)) (.leaf (-4)))),
  (.branch 28 (.branch 26 (.branch 9 (.leaf (-17)) (.leaf (-16))) (.branch 27 (.leaf (-14)) (.leaf (-12)))) (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-8))) (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-4)) (.leaf (-2)))))),
  (.leaf (0))]
def witnessD6_007_171 : CycleWitness 6 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (0)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (1))) (.branch 19 (.leaf (2)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (4))))))))
  code := certificateD6_171
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 26 (.leaf (7)) (.branch 30 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 22 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 26 (.leaf (-18)) (.leaf (-22)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 14 (.leaf (-9)) (.branch 18 (.leaf (-10)) (.leaf (-11))))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (-13)) (.leaf (-17)))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (-13))) (.branch 21 (.leaf (-14)) (.branch 29 (.leaf (-15)) (.leaf (-16))))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-4)) (.leaf (-5))))]
  high := ![(.branch 31 (.branch 27 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-16)) (.leaf (-11)))),
  (.branch 19 (.leaf (-11)) (.branch 28 (.leaf (-10)) (.leaf (-8)))),
  (.branch 26 (.branch 20 (.leaf (-17)) (.leaf (-15))) (.branch 32 (.leaf (-13)) (.leaf (-8)))),
  (.branch 31 (.branch 30 (.leaf (-16)) (.leaf (-12))) (.branch 32 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 30 (.branch 29 (.leaf (-5)) (.leaf (-4))) (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_007_172 : CycleWitness 6 where
  length := 33
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (2))) (.branch 19 (.leaf (5)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (3)) (.leaf (5))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (4)) (.leaf (1))))))))
  code := certificateD6_172
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 17 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-7)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-25))) (.branch 18 (.leaf (-26)) (.branch 26 (.leaf (-27)) (.leaf (-28))))),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 29 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-4)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 29 (.branch 27 (.leaf (-28)) (.branch 28 (.leaf (-24)) (.leaf (-20)))) (.branch 31 (.branch 30 (.leaf (-16)) (.leaf (-12))) (.branch 32 (.leaf (-8)) (.leaf (-4))))),
  (.branch 30 (.branch 5 (.leaf (-17)) (.leaf (-16))) (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-8)) (.leaf (-4))))),
  (.branch 16 (.leaf (-6)) (.leaf (-4))),
  (.branch 31 (.leaf (-3)) (.branch 32 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_007_173 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 15 (.leaf (0)) (.leaf (3))))) (.branch 24 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 31 (.leaf (0)) (.leaf (3))))))
  code := certificateD6_173
  counts := ![(.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.leaf (3)) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 11 (.branch 9 (.leaf (6)) (.branch 10 (.leaf (7)) (.leaf (8)))) (.branch 13 (.leaf (9)) (.branch 14 (.leaf (10)) (.leaf (11)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (12)) (.branch 18 (.leaf (13)) (.leaf (14)))) (.branch 21 (.leaf (15)) (.branch 22 (.leaf (16)) (.leaf (17))))) (.branch 27 (.branch 25 (.leaf (18)) (.branch 26 (.leaf (19)) (.leaf (20)))) (.branch 30 (.branch 29 (.leaf (21)) (.leaf (22))) (.branch 31 (.leaf (23)) (.leaf (24))))))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-1))) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-12))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-4)))]
  high := ![(.leaf (-3)),
  (.branch 26 (.branch 23 (.branch 21 (.leaf (-12)) (.branch 22 (.leaf (-11)) (.leaf (-10)))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-20)) (.leaf (-19))) (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16))))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_007_174 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 12 (.branch 10 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (5)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (1))))) (.branch 28 (.branch 26 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.leaf (1)))))))
  code := certificateD6_174
  counts := ![(.branch 14 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 22 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 26 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 28 (.leaf (14)) (.branch 30 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 15 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 23 (.leaf (0)) (.leaf (-9))),
  (.branch 31 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-25)) (.branch 9 (.leaf (-24)) (.leaf (-23)))) (.branch 11 (.leaf (-22)) (.branch 12 (.leaf (-21)) (.leaf (-20))))) (.branch 16 (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17)))) (.branch 17 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_007_175 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (5))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_175
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 20 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-7)) (.leaf (-14)))) (.branch 18 (.leaf (-16)) (.branch 20 (.leaf (-18)) (.leaf (-20))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-22))),
  (.branch 26 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 26 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 31 (.leaf (-18)) (.leaf (-13)))),
  (.branch 30 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 21 (.branch 15 (.branch 12 (.branch 11 (.leaf (-22)) (.leaf (-21))) (.branch 13 (.leaf (-20)) (.branch 14 (.leaf (-19)) (.leaf (-18))))) (.branch 18 (.branch 16 (.leaf (-17)) (.branch 17 (.leaf (-16)) (.leaf (-15)))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_007_176 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_176
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (7))))) (.branch 22 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 26 (.branch 24 (.leaf (12)) (.leaf (13))) (.branch 28 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 20 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_007_177 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (5)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_177
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 20 (.leaf (10)) (.leaf (11)))) (.branch 27 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 29 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 21 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-27))),
  (.branch 21 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 21 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-8)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.branch 11 (.branch 8 (.branch 6 (.leaf (-27)) (.branch 7 (.leaf (-26)) (.leaf (-25)))) (.branch 9 (.leaf (-24)) (.branch 10 (.leaf (-23)) (.leaf (-22))))) (.branch 14 (.branch 12 (.leaf (-21)) (.branch 13 (.leaf (-20)) (.leaf (-19)))) (.branch 16 (.branch 15 (.leaf (-18)) (.leaf (-17))) (.branch 17 (.leaf (-16)) (.leaf (-15)))))) (.branch 25 (.branch 21 (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))) (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_007_178 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_178
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 17 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 18 (.leaf (-18)) (.leaf (-22)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 9 (.leaf (-2)) (.branch 12 (.leaf (-3)) (.leaf (-4))))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-19))),
  (.branch 29 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 25 (.branch 19 (.leaf (-22)) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 28 (.leaf (-19)) (.branch 31 (.leaf (-18)) (.leaf (-13))))),
  (.branch 29 (.leaf (-4)) (.leaf (0))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-19)) (.leaf (-18))) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_007_179 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (3)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_179
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 13 (.leaf (-8)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.branch 26 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-5)))),
  (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD6_007_180 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (2)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (3))) (.branch 23 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (0))) (.branch 27 (.leaf (1)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (2))) (.branch 31 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_180
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-14)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-10))),
  (.branch 13 (.leaf (0)) (.leaf (-19))),
  (.branch 29 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 29 (.leaf (-16)) (.leaf (-13)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-19)) (.leaf (-18))) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_007_181 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.leaf (4)) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (1)))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (0)))) (.branch 22 (.branch 21 (.leaf (2)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.leaf (5)) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_181
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 9 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 11 (.leaf (6)) (.branch 13 (.leaf (7)) (.leaf (8)))))) (.branch 24 (.branch 18 (.branch 17 (.leaf (9)) (.leaf (10))) (.branch 20 (.leaf (11)) (.branch 22 (.leaf (12)) (.leaf (13))))) (.branch 27 (.branch 25 (.leaf (14)) (.leaf (15))) (.branch 29 (.leaf (16)) (.branch 31 (.leaf (17)) (.leaf (18))))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.leaf (0)) (.leaf (-22))),
  (.branch 26 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 26 (.leaf (-15)) (.leaf (-13))) (.branch 30 (.leaf (-11)) (.leaf (-9)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 29 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 11 (.leaf (-22)) (.leaf (-21))) (.branch 13 (.leaf (-20)) (.branch 14 (.leaf (-19)) (.leaf (-18))))) (.branch 18 (.branch 16 (.leaf (-17)) (.branch 17 (.leaf (-16)) (.leaf (-15)))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_007_182 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (1)))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (0)) (.branch 19 (.leaf (3)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (5)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_182
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 23 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 25 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 6 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 20 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 18 (.leaf (-8)) (.leaf (-9)))),
  (.branch 6 (.leaf (0)) (.branch 22 (.leaf (-2)) (.leaf (-3)))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 26 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-5)))),
  (.branch 23 (.leaf (-3)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-1)),
  (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_007_183 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (2))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.leaf (2)))))))
  code := certificateD6_183
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 21 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 30 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-11)) (.branch 14 (.leaf (-13)) (.leaf (-14))))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 20 (.leaf (-14)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-9))),
  (.branch 15 (.leaf (0)) (.leaf (-17))),
  (.branch 31 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 31 (.leaf (-14)) (.leaf (-7))),
  (.branch 30 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 31 (.leaf (-14)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 19 (.branch 17 (.branch 16 (.leaf (-17)) (.leaf (-16))) (.branch 18 (.leaf (-15)) (.leaf (-14)))) (.branch 21 (.branch 20 (.leaf (-13)) (.leaf (-12))) (.branch 22 (.leaf (-11)) (.leaf (-10))))) (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD6_007_184 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (1)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (1)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (2))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_184
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-2)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 13 (.leaf (0)) (.leaf (-19))),
  (.branch 29 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 28 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 22 (.branch 17 (.branch 15 (.branch 14 (.leaf (-19)) (.leaf (-18))) (.branch 16 (.leaf (-17)) (.leaf (-16)))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_007_185 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_185
  counts := ![(.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 27 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 29 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.branch 16 (.leaf (0)) (.leaf (-16))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 31 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.leaf (-13)))) (.branch 22 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 23 (.leaf (-10)) (.leaf (-9))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD6_007_186 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (0)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (3)))) (.branch 22 (.branch 21 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (1)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (0)) (.leaf (5)))))))
  code := certificateD6_186
  counts := ![(.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 27 (.branch 25 (.leaf (12)) (.leaf (13))) (.branch 29 (.leaf (14)) (.branch 31 (.leaf (15)) (.leaf (16))))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-7)) (.leaf (-8)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (-1))) (.branch 30 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-8))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 29 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-8)) (.branch 31 (.leaf (-6)) (.leaf (-4))))),
  (.branch 28 (.branch 15 (.leaf (-8)) (.branch 27 (.leaf (-7)) (.leaf (-6)))) (.branch 30 (.branch 29 (.leaf (-5)) (.leaf (-4))) (.branch 31 (.leaf (-3)) (.leaf (-2))))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 28 (.branch 26 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD6_007_187 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (1)) (.leaf (0))) (.branch 27 (.leaf (5)) (.leaf (2)))) (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_187
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 29 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-21))),
  (.branch 27 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-11)) (.branch 27 (.leaf (-10)) (.leaf (-7)))),
  (.branch 26 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 21 (.branch 16 (.branch 13 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17))))) (.branch 18 (.branch 17 (.leaf (-16)) (.leaf (-15))) (.branch 19 (.leaf (-14)) (.branch 20 (.leaf (-13)) (.leaf (-12)))))) (.branch 26 (.branch 23 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 24 (.leaf (-9)) (.branch 25 (.leaf (-8)) (.leaf (-7))))) (.branch 29 (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-5)) (.leaf (-4)))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_007_188 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (1)) (.leaf (0))) (.branch 23 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (2)) (.leaf (1))) (.branch 27 (.leaf (0)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_188
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 8 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-20))),
  (.branch 28 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 28 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.leaf (-5)) (.leaf (-3))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.branch 17 (.branch 14 (.branch 13 (.leaf (-20)) (.leaf (-19))) (.branch 15 (.leaf (-18)) (.branch 16 (.leaf (-17)) (.leaf (-16))))) (.branch 19 (.branch 18 (.leaf (-15)) (.leaf (-14))) (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))))) (.branch 27 (.branch 24 (.branch 23 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.branch 26 (.leaf (-7)) (.leaf (-6))))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_007_189 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (5))) (.branch 15 (.leaf (0)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (0))) (.branch 23 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (3)) (.leaf (0))) (.branch 27 (.leaf (2)) (.leaf (0)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (5))) (.branch 31 (.leaf (0)) (.leaf (4)))))))
  code := certificateD6_189
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 12 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 17 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 28 (.branch 26 (.leaf (11)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 25 (.leaf (-6)) (.leaf (-8)))),
  (.branch 9 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 29 (.leaf (-12)) (.leaf (-7))),
  (.branch 30 (.branch 24 (.leaf (-11)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 26 (.leaf (-8)) (.branch 27 (.leaf (-7)) (.leaf (-6)))) (.branch 30 (.branch 29 (.leaf (-5)) (.leaf (-4))) (.branch 31 (.leaf (-3)) (.leaf (-2))))),
  (.branch 10 (.leaf (-2)) (.branch 22 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_007_190 : CycleWitness 6 where
  length := 32
  word := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (0)) (.leaf (2)))) (.branch 22 (.branch 21 (.leaf (3)) (.leaf (0))) (.branch 23 (.leaf (5)) (.leaf (1))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (0)) (.leaf (2))) (.branch 27 (.leaf (0)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (3)))))))
  code := certificateD6_190
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 17 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 27 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 30 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 18 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.leaf (-10))),
  (.branch 4 (.leaf (0)) (.leaf (-4))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-25))),
  (.branch 23 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 28 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-6)) (.leaf (-3)))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 29 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 19 (.branch 13 (.branch 10 (.branch 8 (.leaf (-25)) (.branch 9 (.leaf (-24)) (.leaf (-23)))) (.branch 11 (.leaf (-22)) (.branch 12 (.leaf (-21)) (.leaf (-20))))) (.branch 16 (.branch 14 (.leaf (-19)) (.branch 15 (.leaf (-18)) (.leaf (-17)))) (.branch 17 (.leaf (-16)) (.branch 18 (.leaf (-15)) (.leaf (-14)))))) (.branch 25 (.branch 22 (.branch 20 (.leaf (-13)) (.branch 21 (.leaf (-12)) (.leaf (-11)))) (.branch 23 (.leaf (-10)) (.branch 24 (.leaf (-9)) (.leaf (-8))))) (.branch 28 (.branch 26 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))) (.branch 30 (.branch 29 (.leaf (-4)) (.leaf (-3))) (.branch 31 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 26 (.leaf (-7)) (.leaf (-6)))) (.branch 29 (.branch 28 (.leaf (-5)) (.leaf (-4))) (.branch 30 (.leaf (-3)) (.branch 31 (.leaf (-2)) (.leaf (-1))))))]
def witnessD6_007 : Fin 30 → CycleWitness 6 := ![witnessD6_007_161, witnessD6_007_162, witnessD6_007_163, witnessD6_007_164, witnessD6_007_165, witnessD6_007_166, witnessD6_007_167, witnessD6_007_168, witnessD6_007_169, witnessD6_007_170, witnessD6_007_171, witnessD6_007_172, witnessD6_007_173, witnessD6_007_174, witnessD6_007_175, witnessD6_007_176, witnessD6_007_177, witnessD6_007_178, witnessD6_007_179, witnessD6_007_180, witnessD6_007_181, witnessD6_007_182, witnessD6_007_183, witnessD6_007_184, witnessD6_007_185, witnessD6_007_186, witnessD6_007_187, witnessD6_007_188, witnessD6_007_189, witnessD6_007_190]
end RealPinwheel.FiveSixths


