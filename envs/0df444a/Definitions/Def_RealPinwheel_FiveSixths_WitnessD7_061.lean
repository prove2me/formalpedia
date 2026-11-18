-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_061
-- name    : RealPinwheel_FiveSixths_WitnessD7_061
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:08:19.201397+00:00
-- url     : https://prove2.me/theorems/31822975-d9f0-4add-a5ec-1175aaa3ff0b
-- title:
--   Exact witness block D7_061
-- statement:
--   These exact witnesses represent words 1129 through 1161 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1129–1161; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_061_1128 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (3))) (.branch 14 (.leaf (0)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (6))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (3)) (.leaf (4)))))))
  code := certificateD7_1128
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 9 (.leaf (-25)) (.branch 26 (.leaf (-27)) (.leaf (-28))))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-3)) (.leaf (-4)))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-26))),
  (.branch 20 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 28 (.branch 27 (.leaf (-28)) (.leaf (-21))) (.branch 29 (.leaf (-14)) (.leaf (-7)))),
  (.branch 20 (.leaf (-8)) (.branch 29 (.leaf (-7)) (.leaf (-4)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 14 (.leaf (-4)) (.branch 22 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.branch 16 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 17 (.branch 10 (.branch 7 (.branch 5 (.leaf (-26)) (.branch 6 (.leaf (-25)) (.leaf (-24)))) (.branch 8 (.leaf (-23)) (.branch 9 (.leaf (-22)) (.leaf (-21))))) (.branch 13 (.branch 11 (.leaf (-20)) (.branch 12 (.leaf (-19)) (.leaf (-18)))) (.branch 15 (.branch 14 (.leaf (-17)) (.leaf (-16))) (.branch 16 (.leaf (-15)) (.leaf (-14)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-13)) (.branch 19 (.leaf (-12)) (.leaf (-11)))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_061_1129 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1129
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-4)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1130 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (1))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_1130
  counts := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 20 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 18 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_061_1131 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (6)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (2))) (.branch 29 (.leaf (0)) (.leaf (3)))))))
  code := certificateD7_1131
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_061_1132 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (1)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1132
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-2))) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 15 (.leaf (0)) (.leaf (-15))),
  (.leaf (0))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 22 (.branch 18 (.branch 16 (.leaf (-15)) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_061_1133 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (2))) (.branch 6 (.leaf (1)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (1)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (4)))))))
  code := certificateD7_1133
  counts := ![(.branch 12 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 17 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 29 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-11)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 5 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 24 (.branch 20 (.leaf (-14)) (.leaf (-13))) (.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 22 (.branch 18 (.leaf (-7)) (.leaf (-6))) (.branch 26 (.leaf (-5)) (.leaf (-4)))),
  (.branch 21 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17))))) (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1134 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (1)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (4))) (.branch 10 (.leaf (0)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (5))) (.branch 21 (.leaf (1)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (3))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1134
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-10))),
  (.branch 12 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 26 (.branch 4 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.branch 24 (.leaf (-7)) (.leaf (-6))))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_061_1135 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (4)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (4)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (2)))))))
  code := certificateD7_1135
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.leaf (-22))),
  (.branch 23 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 19 (.branch 13 (.branch 10 (.branch 9 (.leaf (-22)) (.leaf (-21))) (.branch 11 (.leaf (-20)) (.branch 12 (.leaf (-19)) (.leaf (-18))))) (.branch 16 (.branch 14 (.leaf (-17)) (.branch 15 (.leaf (-16)) (.leaf (-15)))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1136 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (0))) (.branch 25 (.leaf (3)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.leaf (5)))))))
  code := certificateD7_1136
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 21 (.leaf (-6)) (.branch 26 (.leaf (-7)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 14 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-9)) (.leaf (-8))) (.branch 29 (.leaf (-7)) (.leaf (-6)))),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (-1)),
  (.branch 15 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 24 (.branch 7 (.leaf (-10)) (.leaf (-9))) (.branch 25 (.leaf (-8)) (.leaf (-7)))) (.branch 28 (.branch 27 (.leaf (-6)) (.leaf (-5))) (.branch 29 (.leaf (-4)) (.leaf (-3)))))]
def witnessD7_061_1137 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (2)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (3))) (.branch 14 (.leaf (6)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (5))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1137
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 9 (.leaf (0)) (.leaf (-6))),
  (.branch 14 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 22 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_061_1138 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (5))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (2))) (.branch 14 (.leaf (1)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (2)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (6))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (3)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (3))) (.branch 29 (.leaf (5)) (.leaf (2)))))))
  code := certificateD7_1138
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 15 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-1)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 18 (.leaf (-7)) (.branch 25 (.leaf (-4)) (.leaf (0)))),
  (.branch 29 (.leaf (-11)) (.leaf (-8))),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1139 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (0))) (.branch 10 (.leaf (3)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (6))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (2)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (5)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (4)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (6))) (.branch 29 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1139
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-14))) (.branch 19 (.leaf (-16)) (.leaf (-19)))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 11 (.leaf (0)) (.leaf (-6))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 24 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 28 (.leaf (-17)) (.branch 29 (.leaf (-12)) (.leaf (-7))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 12 (.leaf (-6)) (.branch 25 (.leaf (-4)) (.leaf (0)))),
  (.branch 23 (.leaf (-8)) (.leaf (-7))),
  (.branch 27 (.branch 5 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_061_1140 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (3)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (6))) (.branch 10 (.leaf (3)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (5))) (.branch 14 (.leaf (1)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (4))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (6))) (.branch 25 (.leaf (3)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (4)))))))
  code := certificateD7_1140
  counts := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-9)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 19 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 27 (.branch 26 (.leaf (-10)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 20 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1141 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (1))) (.branch 10 (.leaf (0)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (6)))))))
  code := certificateD7_1141
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 16 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 25 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0))]
  high := ![(.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 24 (.branch 13 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0))]
def witnessD7_061_1142 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (3)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (5))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (3))) (.branch 21 (.leaf (0)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1142
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 13 (.leaf (0)) (.leaf (-17))),
  (.branch 23 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 22 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.leaf (0)),
  (.branch 16 (.branch 9 (.branch 6 (.branch 4 (.leaf (-27)) (.branch 5 (.leaf (-26)) (.leaf (-25)))) (.branch 7 (.leaf (-24)) (.branch 8 (.leaf (-23)) (.leaf (-22))))) (.branch 12 (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19)))) (.branch 14 (.branch 13 (.leaf (-18)) (.leaf (-17))) (.branch 15 (.leaf (-16)) (.leaf (-15)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))) (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 21 (.branch 17 (.branch 15 (.branch 14 (.leaf (-17)) (.leaf (-16))) (.branch 16 (.leaf (-15)) (.leaf (-14)))) (.branch 19 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 20 (.leaf (-11)) (.leaf (-10))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1143 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (6)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (4))) (.branch 14 (.leaf (1)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (6)) (.leaf (1)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1143
  counts := ![(.branch 12 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 12 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 28 (.leaf (-12)) (.branch 29 (.leaf (-8)) (.leaf (-4)))),
  (.branch 27 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.leaf (-2)) (.leaf (-1))),
  (.branch 23 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1144 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (6)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (5)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (4))) (.branch 14 (.leaf (3)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (0)) (.leaf (6)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (0))) (.branch 29 (.leaf (3)) (.leaf (5)))))))
  code := certificateD7_1144
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 28 (.leaf (8)) (.leaf (9)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 22 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.branch 20 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_061_1145 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (0))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (6)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (0))) (.branch 21 (.leaf (3)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (0))) (.branch 25 (.leaf (4)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1145
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 20 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 24 (.leaf (6)) (.branch 28 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 18 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-27))),
  (.branch 18 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 21 (.branch 17 (.leaf (-11)) (.leaf (-10))) (.branch 25 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 24 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 16 (.branch 9 (.branch 6 (.branch 4 (.leaf (-27)) (.branch 5 (.leaf (-26)) (.leaf (-25)))) (.branch 7 (.leaf (-24)) (.branch 8 (.leaf (-23)) (.leaf (-22))))) (.branch 12 (.branch 10 (.leaf (-21)) (.branch 11 (.leaf (-20)) (.leaf (-19)))) (.branch 14 (.branch 13 (.leaf (-18)) (.leaf (-17))) (.branch 15 (.leaf (-16)) (.leaf (-15)))))) (.branch 23 (.branch 19 (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))) (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 21 (.branch 19 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_061_1146 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (1))) (.branch 6 (.leaf (4)) (.leaf (2))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (0)) (.leaf (2))) (.branch 14 (.leaf (4)) (.leaf (1)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (2)) (.leaf (1))) (.branch 21 (.leaf (4)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (6))) (.branch 25 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (4)) (.leaf (1)))))))
  code := certificateD7_1146
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 18 (.branch 16 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-21))),
  (.branch 24 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 28 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 29 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 27 (.branch 20 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 19 (.branch 14 (.branch 11 (.branch 10 (.leaf (-21)) (.leaf (-20))) (.branch 12 (.leaf (-19)) (.branch 13 (.leaf (-18)) (.leaf (-17))))) (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.branch 18 (.leaf (-13)) (.leaf (-12)))))) (.branch 24 (.branch 21 (.branch 20 (.leaf (-11)) (.leaf (-10))) (.branch 22 (.leaf (-9)) (.branch 23 (.leaf (-8)) (.leaf (-7))))) (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1147 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (2))) (.branch 10 (.leaf (0)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (5)) (.leaf (3)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_1147
  counts := ![(.branch 13 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 10 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))) (.branch 25 (.branch 23 (.leaf (9)) (.leaf (10))) (.branch 28 (.leaf (11)) (.leaf (12)))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 10 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 14 (.leaf (0)) (.leaf (-16))),
  (.branch 29 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 26 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-10)) (.leaf (-8)))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 22 (.branch 18 (.branch 16 (.branch 15 (.leaf (-16)) (.leaf (-15))) (.branch 17 (.leaf (-14)) (.leaf (-13)))) (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.leaf (-9))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_061_1148 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (2)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (2)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (5)) (.leaf (3))) (.branch 25 (.leaf (1)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (4)) (.leaf (6)))))))
  code := certificateD7_1148
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.leaf (7))))),
  (.branch 11 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 9 (.leaf (-25)) (.branch 13 (.leaf (-27)) (.leaf (-29))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 28 (.leaf (-5)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-6))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 27 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-14)) (.leaf (-7))))),
  (.branch 29 (.leaf (-7)) (.leaf (-4))),
  (.branch 28 (.branch 22 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 25 (.leaf (-6)) (.branch 26 (.leaf (-5)) (.leaf (-4)))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_061_1149 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (0))) (.branch 6 (.leaf (5)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (0))) (.branch 10 (.leaf (4)) (.leaf (3)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (2))) (.branch 14 (.leaf (0)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (5)) (.leaf (0))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (3)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.leaf (6)))))))
  code := certificateD7_1149
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 23 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 28 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-23))) (.branch 9 (.leaf (-25)) (.leaf (-27)))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 24 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 23 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.leaf (-12)) (.leaf (-7))),
  (.branch 18 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2)))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_061_1150 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (0)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (2))) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (3))) (.branch 14 (.leaf (1)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (3)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (6)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (0)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (2))) (.branch 29 (.leaf (5)) (.leaf (1)))))))
  code := certificateD7_1150
  counts := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 19 (.leaf (-8)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 17 (.leaf (-5)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.leaf (-1)) (.leaf (0))),
  (.branch 16 (.branch 3 (.leaf (-13)) (.leaf (-12))) (.branch 29 (.leaf (-11)) (.leaf (-8)))),
  (.branch 28 (.branch 20 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-8)) (.leaf (-5)))),
  (.branch 27 (.branch 26 (.leaf (-7)) (.leaf (-6))) (.branch 28 (.leaf (-5)) (.branch 29 (.leaf (-4)) (.leaf (-3))))),
  (.branch 19 (.leaf (-2)) (.leaf (-1))),
  (.branch 26 (.branch 24 (.branch 8 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1151 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (3))) (.branch 10 (.leaf (6)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (4)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (0)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (4))) (.branch 21 (.leaf (2)) (.leaf (1))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (0)) (.leaf (3))) (.branch 25 (.leaf (6)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (5))) (.branch 29 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_1151
  counts := ![(.branch 11 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 15 (.leaf (4)) (.leaf (5))) (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-20)) (.leaf (-33)))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 22 (.leaf (-4)) (.leaf (-6)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 16 (.leaf (-12)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-11)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-2))),
  (.branch 10 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 16 (.branch 8 (.branch 4 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 24 (.branch 20 (.leaf (-29)) (.leaf (-28))) (.branch 28 (.leaf (-27)) (.branch 29 (.leaf (-20)) (.leaf (-13)))))),
  (.branch 25 (.branch 23 (.leaf (-6)) (.branch 24 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.branch 26 (.leaf (-3)) (.leaf (-2))) (.branch 28 (.leaf (-1)) (.leaf (0))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 17 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-10)))) (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-6))) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.branch 27 (.leaf (-14)) (.leaf (-11))) (.branch 29 (.leaf (-8)) (.leaf (-5)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_061_1152 : CycleWitness 7 where
  length := 30
  word := (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (6)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (3))) (.branch 10 (.leaf (1)) (.leaf (4)))) (.branch 13 (.branch 12 (.leaf (2)) (.leaf (0))) (.branch 14 (.leaf (3)) (.leaf (5)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (3))) (.branch 21 (.leaf (6)) (.leaf (5))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (1)) (.leaf (2))) (.branch 25 (.leaf (0)) (.leaf (4)))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (5)))))))
  code := certificateD7_1152
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 27 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 26 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 22 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 28 (.branch 21 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.leaf (-1)))),
  (.branch 27 (.branch 19 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-6)) (.branch 29 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 23 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 24 (.leaf (-7)) (.leaf (-6)))) (.branch 27 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.branch 29 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_061_1153 : CycleWitness 7 where
  length := 29
  word := (.branch 15 (.branch 8 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (6)) (.leaf (0))))) (.branch 11 (.branch 9 (.leaf (3)) (.branch 10 (.leaf (1)) (.leaf (0)))) (.branch 13 (.branch 12 (.leaf (5)) (.leaf (0))) (.branch 14 (.leaf (2)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3)))) (.branch 20 (.branch 19 (.leaf (0)) (.leaf (6))) (.branch 21 (.leaf (2)) (.leaf (0))))) (.branch 25 (.branch 23 (.leaf (4)) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (5)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (2)))))))
  code := certificateD7_1153
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 8 (.leaf (3)) (.branch 11 (.leaf (4)) (.leaf (5))))) (.branch 22 (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 24 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-12)) (.leaf (-24)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.leaf (-19)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-2)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (-6)) (.leaf (-7)))),
  (.branch 12 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10))))]
  high := ![(.branch 14 (.branch 3 (.leaf (-24)) (.leaf (-23))) (.branch 25 (.leaf (-22)) (.branch 28 (.leaf (-20)) (.leaf (-13))))),
  (.branch 26 (.branch 18 (.leaf (-19)) (.leaf (-16))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-8)) (.leaf (-4))))),
  (.branch 7 (.leaf (-4)) (.branch 22 (.leaf (-3)) (.leaf (0)))),
  (.branch 19 (.leaf (-4)) (.leaf (-3))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2))))),
  (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 23 (.leaf (-8)) (.leaf (-7)))) (.branch 26 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2))))))]
def witnessD7_061_1154 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (2))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.leaf (0)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (1)))))))
  code := certificateD7_1154
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 21 (.branch 16 (.leaf (6)) (.branch 19 (.leaf (7)) (.leaf (8)))) (.branch 24 (.leaf (9)) (.branch 27 (.leaf (10)) (.leaf (11)))))),
  (.branch 15 (.branch 4 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 22 (.branch 18 (.leaf (5)) (.leaf (6))) (.branch 25 (.leaf (7)) (.branch 29 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 20 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 16 (.leaf (-17)) (.branch 21 (.leaf (-21)) (.leaf (-24))))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-10)) (.leaf (-20)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.branch 23 (.leaf (-5)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-24))),
  (.branch 20 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 25 (.branch 22 (.leaf (-24)) (.leaf (-22))) (.branch 28 (.leaf (-20)) (.leaf (-13)))),
  (.branch 19 (.branch 5 (.leaf (-20)) (.branch 12 (.leaf (-19)) (.leaf (-18)))) (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-10))) (.branch 28 (.leaf (-3)) (.leaf (0))))),
  (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2))))),
  (.branch 17 (.branch 11 (.branch 8 (.branch 6 (.leaf (-24)) (.branch 7 (.leaf (-23)) (.leaf (-22)))) (.branch 9 (.leaf (-21)) (.branch 10 (.leaf (-20)) (.leaf (-19))))) (.branch 14 (.branch 12 (.leaf (-18)) (.branch 13 (.leaf (-17)) (.leaf (-16)))) (.branch 15 (.leaf (-15)) (.branch 16 (.leaf (-14)) (.leaf (-13)))))) (.branch 23 (.branch 20 (.branch 18 (.leaf (-12)) (.branch 19 (.leaf (-11)) (.leaf (-10)))) (.branch 21 (.leaf (-9)) (.branch 22 (.leaf (-8)) (.leaf (-7))))) (.branch 26 (.branch 24 (.leaf (-6)) (.branch 25 (.leaf (-5)) (.leaf (-4)))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 24 (.branch 22 (.branch 21 (.leaf (-9)) (.leaf (-8))) (.branch 23 (.leaf (-7)) (.leaf (-6)))) (.branch 26 (.branch 25 (.leaf (-5)) (.leaf (-4))) (.branch 27 (.leaf (-3)) (.branch 28 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_061_1155 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (4))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (0)) (.leaf (3)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (1)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1155
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-19)) (.leaf (-28)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 17 (.leaf (-8)) (.leaf (-11)))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-11)) (.leaf (-17)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 8 (.leaf (0)) (.branch 22 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 16 (.branch 7 (.branch 4 (.leaf (-28)) (.leaf (-27))) (.branch 10 (.leaf (-26)) (.branch 13 (.leaf (-25)) (.leaf (-24))))) (.branch 22 (.branch 19 (.leaf (-23)) (.leaf (-22))) (.branch 25 (.leaf (-21)) (.branch 28 (.leaf (-20)) (.leaf (-10)))))),
  (.branch 27 (.branch 8 (.leaf (-5)) (.leaf (-4))) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.branch 18 (.leaf (-11)) (.leaf (-10))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-6)) (.leaf (-4))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 26 (.branch 24 (.leaf (-17)) (.branch 25 (.leaf (-15)) (.leaf (-13)))) (.branch 27 (.leaf (-11)) (.branch 28 (.leaf (-9)) (.leaf (-7))))),
  (.branch 14 (.leaf (-3)) (.leaf (-2))),
  (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_061_1156 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (3))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (4)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (6)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (4)) (.leaf (1)))) (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (6)) (.leaf (2)))))))
  code := certificateD7_1156
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 18 (.leaf (6)) (.leaf (7)))) (.branch 23 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 19 (.leaf (3)) (.branch 25 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-2))) (.branch 23 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-19)) (.leaf (-21)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-8)) (.leaf (-10)))),
  (.branch 10 (.leaf (0)) (.branch 24 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.leaf (-19))),
  (.branch 13 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 24 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2)))),
  (.branch 26 (.branch 20 (.leaf (-21)) (.leaf (-20))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 27 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 21 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-16)) (.branch 23 (.leaf (-14)) (.leaf (-12))))) (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 14 (.leaf (-3)) (.leaf (-2)))]
def witnessD7_061_1157 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (2)) (.leaf (6))) (.branch 6 (.leaf (0)) (.leaf (4))))) (.branch 10 (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (4)))) (.branch 19 (.branch 18 (.leaf (2)) (.leaf (0))) (.branch 20 (.leaf (6)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2)))) (.branch 27 (.branch 26 (.leaf (4)) (.leaf (0))) (.branch 28 (.leaf (5)) (.leaf (3)))))))
  code := certificateD7_1157
  counts := ![(.branch 12 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 27 (.leaf (9)) (.leaf (10)))))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 23 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-21))) (.branch 16 (.leaf (-22)) (.branch 23 (.leaf (-23)) (.leaf (-24))))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-13))) (.branch 18 (.leaf (-14)) (.branch 25 (.leaf (-15)) (.leaf (-16))))),
  (.branch 14 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-8)) (.leaf (-9)))),
  (.branch 13 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-19)))]
  high := ![(.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 26 (.branch 24 (.leaf (-24)) (.branch 25 (.leaf (-20)) (.leaf (-16)))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-8)) (.leaf (-4))))),
  (.branch 27 (.branch 26 (.leaf (-16)) (.leaf (-12))) (.branch 28 (.leaf (-8)) (.leaf (-4)))),
  (.branch 15 (.leaf (-2)) (.leaf (0))),
  (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3)))),
  (.branch 14 (.leaf (-3)) (.leaf (-2))),
  (.branch 24 (.branch 21 (.branch 6 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-16)) (.branch 23 (.leaf (-14)) (.leaf (-12))))) (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-8))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2))))))]
def witnessD7_061_1158 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (4))) (.branch 6 (.leaf (3)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (6)) (.branch 9 (.leaf (0)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (3)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (4)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (5))) (.branch 20 (.leaf (3)) (.leaf (1))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (2)) (.leaf (4)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (0))) (.branch 28 (.leaf (3)) (.leaf (5)))))))
  code := certificateD7_1158
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.leaf (7))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 21 (.branch 16 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (5)) (.leaf (6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 24 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 28 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-17)) (.leaf (-24)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-17)) (.leaf (-20)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-17))) (.branch 17 (.leaf (-18)) (.branch 24 (.leaf (-19)) (.leaf (-20))))),
  (.branch 6 (.leaf (0)) (.branch 20 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 19 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 14 (.branch 5 (.leaf (-24)) (.leaf (-23))) (.branch 23 (.leaf (-22)) (.branch 28 (.leaf (-19)) (.leaf (-14))))),
  (.branch 22 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 27 (.leaf (-18)) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.branch 26 (.branch 25 (.leaf (-20)) (.leaf (-16))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-8)) (.leaf (-4))))),
  (.branch 21 (.leaf (-6)) (.leaf (-4))),
  (.branch 26 (.branch 6 (.leaf (-14)) (.branch 16 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 9 (.leaf (-13)) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_061_1159 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (5))) (.branch 6 (.leaf (0)) (.leaf (1))))) (.branch 10 (.branch 8 (.leaf (4)) (.branch 9 (.leaf (2)) (.leaf (0)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (1))) (.branch 13 (.leaf (0)) (.leaf (2)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (0)) (.branch 16 (.leaf (6)) (.leaf (1)))) (.branch 19 (.branch 18 (.leaf (5)) (.leaf (0))) (.branch 20 (.leaf (2)) (.leaf (0))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (0)) (.leaf (3)))) (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (6)))))))
  code := certificateD7_1159
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 21 (.branch 15 (.leaf (5)) (.branch 19 (.leaf (6)) (.leaf (7)))) (.branch 24 (.leaf (8)) (.branch 28 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 22 (.branch 17 (.leaf (3)) (.leaf (4))) (.branch 27 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 8 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-17))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-14)) (.leaf (-17)))),
  (.branch 11 (.leaf (0)) (.branch 25 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-10)) (.leaf (-12)))),
  (.leaf (0))]
  high := ![(.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 13 (.branch 3 (.leaf (-17)) (.branch 8 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.branch 18 (.leaf (-14)) (.leaf (-13))) (.branch 28 (.leaf (-12)) (.leaf (-6))))),
  (.branch 21 (.branch 15 (.leaf (-17)) (.leaf (-16))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2)))),
  (.branch 25 (.branch 9 (.leaf (-13)) (.branch 24 (.leaf (-12)) (.leaf (-10)))) (.branch 27 (.branch 26 (.leaf (-8)) (.leaf (-6))) (.branch 28 (.leaf (-4)) (.leaf (-2))))),
  (.branch 23 (.branch 20 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 21 (.leaf (-10)) (.branch 22 (.leaf (-9)) (.leaf (-8))))) (.branch 26 (.branch 24 (.leaf (-7)) (.branch 25 (.leaf (-6)) (.leaf (-5)))) (.branch 27 (.leaf (-4)) (.branch 28 (.leaf (-3)) (.leaf (-2)))))),
  (.leaf (0))]
def witnessD7_061_1160 : CycleWitness 7 where
  length := 29
  word := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (0))))) (.branch 10 (.branch 8 (.leaf (1)) (.branch 9 (.leaf (6)) (.leaf (2)))) (.branch 12 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (0)) (.leaf (1)))))) (.branch 21 (.branch 17 (.branch 15 (.leaf (5)) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 19 (.branch 18 (.leaf (0)) (.leaf (4))) (.branch 20 (.leaf (1)) (.leaf (2))))) (.branch 25 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (6))) (.branch 24 (.leaf (0)) (.leaf (5)))) (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (2)) (.leaf (3)))))))
  code := certificateD7_1160
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 18 (.leaf (3)) (.branch 24 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 20 (.leaf (3)) (.branch 26 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 21 (.leaf (3)) (.branch 28 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-24)) (.leaf (-26)))),
  (.branch 2 (.leaf (0)) (.leaf (-19))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.leaf (0)) (.branch 23 (.leaf (-11)) (.leaf (-12))))]
  high := ![(.branch 26 (.branch 19 (.leaf (-26)) (.branch 25 (.leaf (-25)) (.leaf (-20)))) (.branch 27 (.leaf (-15)) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 15 (.branch 3 (.leaf (-19)) (.branch 9 (.leaf (-18)) (.leaf (-17)))) (.branch 27 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 28 (.leaf (-10)) (.leaf (-5))))),
  (.branch 22 (.leaf (-3)) (.leaf (-2))),
  (.branch 23 (.leaf (-2)) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 20 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 28 (.leaf (-7)) (.leaf (-4)))),
  (.branch 26 (.branch 16 (.leaf (-13)) (.leaf (-12))) (.branch 27 (.leaf (-9)) (.branch 28 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.branch 24 (.leaf (-12)) (.branch 25 (.leaf (-10)) (.leaf (-8)))) (.branch 27 (.leaf (-6)) (.branch 28 (.leaf (-4)) (.leaf (-2)))))]
def witnessD7_061 : Fin 33 → CycleWitness 7 := ![witnessD7_061_1128, witnessD7_061_1129, witnessD7_061_1130, witnessD7_061_1131, witnessD7_061_1132, witnessD7_061_1133, witnessD7_061_1134, witnessD7_061_1135, witnessD7_061_1136, witnessD7_061_1137, witnessD7_061_1138, witnessD7_061_1139, witnessD7_061_1140, witnessD7_061_1141, witnessD7_061_1142, witnessD7_061_1143, witnessD7_061_1144, witnessD7_061_1145, witnessD7_061_1146, witnessD7_061_1147, witnessD7_061_1148, witnessD7_061_1149, witnessD7_061_1150, witnessD7_061_1151, witnessD7_061_1152, witnessD7_061_1153, witnessD7_061_1154, witnessD7_061_1155, witnessD7_061_1156, witnessD7_061_1157, witnessD7_061_1158, witnessD7_061_1159, witnessD7_061_1160]
end RealPinwheel.FiveSixths


