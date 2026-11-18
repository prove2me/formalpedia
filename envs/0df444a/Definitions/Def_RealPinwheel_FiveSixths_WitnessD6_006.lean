-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_006
-- name    : RealPinwheel_FiveSixths_WitnessD6_006
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:22:48.880099+00:00
-- url     : https://prove2.me/theorems/9a92840a-2962-487a-a1f5-9695b2c25eb0
-- title:
--   Exact witness block D6_006
-- statement:
--   These exact witnesses represent words 133 through 161 of source certificate file D6. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 133–161; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D6.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD6
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD6_006_132 : CycleWitness 6 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (1)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (3)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (3)) (.leaf (1))))))))
  code := certificateD6_132
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-7)))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 12 (.leaf (-23)) (.leaf (-24)))) (.branch 27 (.branch 22 (.leaf (-25)) (.leaf (-26))) (.branch 32 (.leaf (-27)) (.leaf (-28))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 29 (.branch 24 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2))))),
  (.branch 27 (.branch 22 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-2)) (.leaf (0))))),
  (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-21))) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 15 (.leaf (-10)) (.leaf (-7))),
  (.branch 25 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_133 : CycleWitness 6 where
  length := 35
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4))))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (3)))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (5)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (2))))))))
  code := certificateD6_133
  counts := ![(.branch 15 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 24 (.leaf (-18)) (.leaf (-24)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-10))) (.branch 10 (.leaf (-17)) (.branch 31 (.leaf (-18)) (.leaf (-19))))),
  (.branch 23 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 14 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (-3)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (-9)) (.leaf (-10))))]
  high := ![(.branch 29 (.branch 25 (.leaf (-24)) (.leaf (-23))) (.branch 33 (.leaf (-22)) (.branch 34 (.leaf (-18)) (.leaf (-14))))),
  (.branch 33 (.branch 32 (.leaf (-19)) (.leaf (-16))) (.branch 34 (.leaf (-13)) (.leaf (-10)))),
  (.branch 24 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.leaf (-5)) (.leaf (-4))),
  (.branch 32 (.branch 31 (.leaf (-10)) (.leaf (-8))) (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-4)) (.leaf (-2)))))]
def witnessD6_006_134 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (2)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (0)))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_134
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.leaf (7)) (.branch 24 (.leaf (8)) (.leaf (9)))) (.branch 31 (.branch 29 (.leaf (10)) (.leaf (11))) (.branch 34 (.leaf (12)) (.leaf (13)))))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-6)) (.leaf (-12)))) (.branch 10 (.branch 6 (.leaf (-13)) (.leaf (-14))) (.branch 23 (.leaf (-16)) (.leaf (-17))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 33 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 24 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-11)))),
  (.branch 32 (.leaf (-3)) (.leaf (0))),
  (.branch 29 (.branch 26 (.branch 8 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1)),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD6_006_135 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (0)) (.leaf (2)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (3)))))))
  code := certificateD6_135
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_136 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (1)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (5)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_136
  counts := ![(.branch 15 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 23 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 21 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (-6))) (.branch 4 (.leaf (-12)) (.leaf (-13)))) (.branch 21 (.branch 19 (.leaf (-14)) (.leaf (-15))) (.branch 23 (.leaf (-16)) (.leaf (-17))))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 14 (.leaf (0)) (.leaf (-20))),
  (.branch 31 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 24 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-11)))),
  (.branch 21 (.leaf (-5)) (.leaf (-4))),
  (.branch 29 (.branch 28 (.leaf (-3)) (.leaf (-2))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 19 (.branch 16 (.branch 15 (.leaf (-20)) (.leaf (-19))) (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16))))) (.branch 21 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_006_137 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (0)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (5)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_137
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-21))),
  (.branch 30 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-21)) (.leaf (-20))) (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17))))) (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_006_138 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (4))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (5))) (.branch 33 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_138
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 18 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 16 (.leaf (-4)) (.leaf (-5)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 29 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-10))),
  (.branch 15 (.leaf (0)) (.leaf (-19))),
  (.branch 32 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-5)),
  (.branch 30 (.leaf (-4)) (.branch 31 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 19 (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_006_139 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (3)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (2))) (.branch 33 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_139
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 18 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 28 (.branch 25 (.leaf (9)) (.leaf (10))) (.branch 31 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 24 (.leaf (-4)) (.branch 31 (.leaf (-3)) (.leaf (0)))),
  (.branch 27 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_140 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (5))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (5))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (4)))))))
  code := certificateD6_140
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-6)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-16))) (.branch 28 (.leaf (-17)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 21 (.leaf (-5)) (.leaf (-4))),
  (.branch 32 (.branch 22 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.branch 29 (.leaf (-18)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_141 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (5)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (2)) (.leaf (1)))))))
  code := certificateD6_141
  counts := ![(.branch 15 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16))))))),
  (.branch 17 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 19 (.leaf (-16)) (.leaf (-17)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-1))) (.branch 23 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 20 (.leaf (-17)) (.branch 33 (.leaf (-16)) (.leaf (-9)))),
  (.branch 28 (.branch 24 (.leaf (-3)) (.leaf (-2))) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.leaf (-2)),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_142 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (1)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (1)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (3)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (1)) (.leaf (5))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (3)) (.leaf (0))) (.branch 33 (.leaf (1)) (.leaf (2)))))))
  code := certificateD6_142
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 7 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 24 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 21 (.leaf (-5)) (.leaf (-4))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 22 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_143 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (0)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.leaf (5)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (3))) (.branch 33 (.leaf (0)) (.leaf (1)))))))
  code := certificateD6_143
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 29 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 27 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-8)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_006_144 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.leaf (1)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (5))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (1)) (.leaf (0))) (.branch 33 (.leaf (3)) (.leaf (1)))))))
  code := certificateD6_144
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 7 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 19 (.leaf (-6)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 20 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.leaf (-4)) (.leaf (-3))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_145 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (0)) (.leaf (1)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (4))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (5))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.leaf (2)))))) (.branch 26 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (0)) (.leaf (1)))) (.branch 32 (.branch 31 (.leaf (0)) (.leaf (4))) (.branch 33 (.leaf (0)) (.leaf (2)))))))
  code := certificateD6_145
  counts := ![(.branch 16 (.branch 6 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 12 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 25 (.branch 19 (.branch 18 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (11)) (.branch 23 (.leaf (12)) (.leaf (13))))) (.branch 29 (.branch 27 (.leaf (14)) (.leaf (15))) (.branch 31 (.leaf (16)) (.branch 33 (.leaf (17)) (.leaf (18))))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-8)) (.leaf (-16)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 26 (.branch 22 (.branch 20 (.leaf (-16)) (.leaf (-15))) (.branch 24 (.leaf (-14)) (.leaf (-13)))) (.branch 30 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 32 (.leaf (-10)) (.leaf (-9))))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 27 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-8)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_146 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (2))))))))
  code := certificateD6_146
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 25 (.branch 20 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 22 (.leaf (9)) (.leaf (10)))) (.branch 30 (.branch 27 (.leaf (11)) (.leaf (12))) (.branch 32 (.leaf (13)) (.leaf (14)))))),
  (.branch 14 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 5 (.leaf (-13)) (.leaf (-16)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 21 (.leaf (-16)) (.leaf (-21)))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-14)) (.leaf (-7)))),
  (.branch 27 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-16)) (.leaf (-13))))),
  (.leaf (0)),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_147 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (4)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (5)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3))))))))
  code := certificateD6_147
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 23 (.branch 18 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-16)))),
  (.branch 4 (.branch 2 (.leaf (0)) (.leaf (-1))) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-23))),
  (.branch 28 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 27 (.branch 21 (.leaf (-16)) (.branch 24 (.leaf (-15)) (.leaf (-14)))) (.branch 30 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-6))))),
  (.leaf (-3)),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 12 (.leaf (-23)) (.leaf (-22))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_148 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (0)) (.leaf (3))))))))
  code := certificateD6_148
  counts := ![(.branch 16 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 30 (.leaf (14)) (.branch 33 (.leaf (15)) (.leaf (16))))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 5 (.leaf (-10)) (.leaf (-11)))) (.branch 11 (.branch 9 (.leaf (-12)) (.leaf (-13))) (.branch 13 (.leaf (-14)) (.leaf (-15))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.leaf (0)) (.leaf (-19))),
  (.branch 32 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 31 (.leaf (-15)) (.leaf (-8))),
  (.branch 32 (.leaf (-12)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-8))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.branch 19 (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 21 (.branch 20 (.leaf (-15)) (.leaf (-14))) (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))))) (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1)))]
def witnessD6_006_149 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (0)) (.leaf (2))))))))
  code := certificateD6_149
  counts := ![(.branch 16 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 31 (.leaf (14)) (.branch 33 (.leaf (15)) (.leaf (16))))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 9 (.branch 7 (.leaf (-11)) (.leaf (-12))) (.branch 11 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.leaf (-14)) (.leaf (-8))),
  (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 28 (.leaf (-3)) (.leaf (-2))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 24 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_150 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (4))))))))
  code := certificateD6_150
  counts := ![(.branch 16 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 24 (.branch 20 (.branch 18 (.leaf (8)) (.leaf (9))) (.branch 22 (.leaf (10)) (.leaf (11)))) (.branch 28 (.branch 26 (.leaf (12)) (.leaf (13))) (.branch 31 (.leaf (14)) (.branch 33 (.leaf (15)) (.leaf (16))))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-10)))) (.branch 9 (.branch 7 (.leaf (-11)) (.leaf (-12))) (.branch 11 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 6 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 27 (.leaf (-8)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.leaf (-14)) (.leaf (-8))),
  (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 24 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 30 (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7)))) (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 23 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_151 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (3))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (5)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (3))))))))
  code := certificateD6_151
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 8 (.leaf (-4)) (.branch 25 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 13 (.leaf (0)) (.leaf (-21))),
  (.branch 30 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 26 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 29 (.branch 28 (.leaf (-3)) (.leaf (-2))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-21)) (.leaf (-20))) (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17))))) (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_006_152 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (5)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (4))))))))
  code := certificateD6_152
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 19 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 7 (.leaf (-14)) (.leaf (-16)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 8 (.leaf (-4)) (.branch 25 (.leaf (-5)) (.leaf (-6))))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-6))) (.branch 27 (.leaf (-7)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 26 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7)))) (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 11 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD6_006_153 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (5)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (4))))))))
  code := certificateD6_153
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 21 (.leaf (-6)) (.leaf (-7)))),
  (.branch 5 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 22 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-19)) (.leaf (-23)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-4)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 22 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 32 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.branch 24 (.branch 10 (.leaf (-23)) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 27 (.leaf (-6)) (.leaf (-5))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_154 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (3))))))))
  code := certificateD6_154
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 21 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 28 (.leaf (11)) (.leaf (12))) (.branch 33 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.leaf (-7)))),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 29 (.branch 28 (.leaf (-3)) (.leaf (-2))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_155 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (0)) (.leaf (4))))))))
  code := certificateD6_155
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 21 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 28 (.leaf (11)) (.leaf (12))) (.branch 33 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 27 (.leaf (-13)) (.leaf (-15)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.leaf (-7)))),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-13)) (.leaf (-11)))) (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-7))) (.branch 33 (.leaf (-5)) (.leaf (-3))))),
  (.branch 11 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (0)))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_156 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (3)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (3)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (5))))))))
  code := certificateD6_156
  counts := ![(.branch 15 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 29 (.branch 26 (.leaf (9)) (.leaf (10))) (.branch 32 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-14)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.branch 33 (.leaf (-5)) (.leaf (-6))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-5))) (.branch 28 (.leaf (-9)) (.leaf (-12)))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 30 (.branch 27 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.leaf (-6)))),
  (.branch 32 (.leaf (-12)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-6)),
  (.branch 31 (.branch 29 (.leaf (-12)) (.branch 30 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7))))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))) (.branch 23 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-10))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD6_006_157 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (3))))))))
  code := certificateD6_157
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 9 (.leaf (0)) (.leaf (-25))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.branch 19 (.leaf (-11)) (.branch 22 (.leaf (-10)) (.leaf (-9)))) (.branch 28 (.leaf (-8)) (.branch 31 (.leaf (-7)) (.leaf (-6))))),
  (.branch 24 (.leaf (-10)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 21 (.branch 15 (.branch 12 (.branch 10 (.leaf (-25)) (.branch 11 (.leaf (-24)) (.leaf (-23)))) (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20))))) (.branch 18 (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17)))) (.branch 19 (.leaf (-16)) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_158 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (1)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (4))))))))
  code := certificateD6_158
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 22 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 25 (.branch 19 (.leaf (-11)) (.branch 22 (.leaf (-10)) (.leaf (-9)))) (.branch 28 (.leaf (-8)) (.branch 31 (.leaf (-7)) (.leaf (-6))))),
  (.branch 24 (.leaf (-10)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 6 (.leaf (-13)) (.branch 18 (.leaf (-12)) (.leaf (-11)))) (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-7))) (.branch 33 (.leaf (-5)) (.leaf (-3))))),
  (.branch 23 (.leaf (-2)) (.leaf (0))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_159 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (3))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (5))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (3))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (1))))))))
  code := certificateD6_159
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 34 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-24))),
  (.branch 27 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 29 (.branch 22 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 31 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.branch 25 (.leaf (-6)) (.leaf (-4))),
  (.branch 32 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 16 (.branch 13 (.branch 11 (.leaf (-24)) (.branch 12 (.leaf (-23)) (.leaf (-22)))) (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19))))) (.branch 19 (.branch 17 (.leaf (-18)) (.branch 18 (.leaf (-17)) (.leaf (-16)))) (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))))) (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006_160 : CycleWitness 6 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (4)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (0)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (4))))))))
  code := certificateD6_160
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-32)) (.leaf (-33)))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-7)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 20 (.leaf (-33)) (.branch 24 (.leaf (-31)) (.leaf (-29)))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-18)) (.leaf (-9))))),
  (.branch 22 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-13)) (.branch 30 (.leaf (-11)) (.leaf (-9))))),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD6_006 : Fin 29 → CycleWitness 6 := ![witnessD6_006_132, witnessD6_006_133, witnessD6_006_134, witnessD6_006_135, witnessD6_006_136, witnessD6_006_137, witnessD6_006_138, witnessD6_006_139, witnessD6_006_140, witnessD6_006_141, witnessD6_006_142, witnessD6_006_143, witnessD6_006_144, witnessD6_006_145, witnessD6_006_146, witnessD6_006_147, witnessD6_006_148, witnessD6_006_149, witnessD6_006_150, witnessD6_006_151, witnessD6_006_152, witnessD6_006_153, witnessD6_006_154, witnessD6_006_155, witnessD6_006_156, witnessD6_006_157, witnessD6_006_158, witnessD6_006_159, witnessD6_006_160]
end RealPinwheel.FiveSixths


