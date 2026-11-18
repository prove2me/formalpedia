-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_050
-- name    : RealPinwheel_FiveSixths_WitnessD7_050
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:03.581209+00:00
-- url     : https://prove2.me/theorems/8d73c102-04b1-48df-8a81-fa3e9947625d
-- title:
--   Exact witness block D7_050
-- statement:
--   These exact witnesses represent words 804 through 830 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 804–830; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_050_803 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (5)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (4)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_803
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 20 (.leaf (-22)) (.leaf (-28)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-19))),
  (.branch 35 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 34 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-22)) (.leaf (-17)))),
  (.branch 22 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (0)))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_050_804 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (4))) (.branch 8 (.leaf (1)) (.leaf (2))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (5))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (1)) (.leaf (2))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (6))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_804
  counts := ![(.branch 14 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-6)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.leaf (0)) (.leaf (-21))),
  (.branch 33 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 20 (.branch 17 (.branch 16 (.leaf (-21)) (.leaf (-20))) (.branch 18 (.leaf (-19)) (.branch 19 (.leaf (-18)) (.leaf (-17))))) (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_050_805 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.leaf (1)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (2)) (.leaf (1))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (5)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (2)) (.leaf (1)))))))
  code := certificateD7_805
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 29 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1))),
  (.branch 13 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 11 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))) (.branch 20 (.leaf (-9)) (.branch 29 (.leaf (-10)) (.leaf (-11))))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-32))),
  (.branch 22 (.leaf (0)) (.leaf (-14))),
  (.branch 31 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-23)))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.leaf (0)),
  (.leaf (-1)),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-32)) (.leaf (-31))) (.branch 7 (.leaf (-30)) (.leaf (-29)))) (.branch 10 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 11 (.leaf (-26)) (.leaf (-25))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-24)) (.leaf (-23))) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-17)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_050_806 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (5))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (4))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (6))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_806
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 6 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 6 (.leaf (-3)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-14))),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 27 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 32 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 25 (.leaf (-6)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_050_807 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (2)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (5)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (3)) (.branch 17 (.leaf (6)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (4)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (5)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_807
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 9 (.leaf (3)) (.branch 12 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 20 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 20 (.leaf (-22)) (.leaf (-28)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 34 (.branch 21 (.leaf (-28)) (.leaf (-27))) (.branch 35 (.leaf (-22)) (.leaf (-17)))),
  (.branch 22 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (0)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_050_808 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (4)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (5))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (6))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (5))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (4)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_808
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-21))) (.branch 17 (.leaf (-22)) (.leaf (-23)))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (-1)) (.leaf (-2)))) (.branch 28 (.leaf (-3)) (.branch 35 (.leaf (-4)) (.leaf (-5))))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 12 (.leaf (-5)) (.leaf (-6)))),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.leaf (0))]
  high := ![(.branch 32 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 33 (.branch 18 (.leaf (-23)) (.leaf (-20))) (.branch 34 (.leaf (-15)) (.branch 35 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-5)),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (0))]
def witnessD7_050_809 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (5)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (1))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (3))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (6)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.leaf (3))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (4)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_809
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 4 (.leaf (0)) (.leaf (-32))),
  (.branch 22 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 32 (.branch 21 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.leaf (-5)),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-32)) (.leaf (-31))) (.branch 7 (.leaf (-30)) (.leaf (-29)))) (.branch 10 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 11 (.leaf (-26)) (.leaf (-25))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-24)) (.leaf (-23))) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-17)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_050_810 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.leaf (0)) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (5))) (.branch 8 (.leaf (0)) (.leaf (3))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (1)) (.leaf (3)))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (0)) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (6))) (.branch 26 (.leaf (0)) (.leaf (3))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (0)))) (.branch 34 (.branch 33 (.leaf (4)) (.leaf (0))) (.branch 35 (.leaf (1)) (.leaf (3)))))))
  code := certificateD7_810
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (3)))) (.branch 10 (.branch 8 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 22 (.leaf (11)) (.branch 25 (.leaf (12)) (.leaf (13))))) (.branch 31 (.branch 28 (.leaf (14)) (.leaf (15))) (.branch 32 (.leaf (16)) (.branch 34 (.leaf (17)) (.leaf (18))))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 6 (.leaf (0)) (.leaf (-30))),
  (.branch 24 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.leaf (-1)),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 21 (.branch 13 (.branch 9 (.branch 7 (.leaf (-30)) (.branch 8 (.leaf (-29)) (.leaf (-28)))) (.branch 11 (.branch 10 (.leaf (-27)) (.leaf (-26))) (.branch 12 (.leaf (-25)) (.leaf (-24))))) (.branch 17 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_050_811 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (0)) (.leaf (4)))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.leaf (5)))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (3))) (.branch 17 (.leaf (0)) (.leaf (1)))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (0)) (.leaf (6)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 35 (.leaf (0)) (.leaf (1)))))))
  code := certificateD7_811
  counts := ![(.branch 17 (.branch 8 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.branch 6 (.leaf (3)) (.leaf (4))))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (10)) (.leaf (11))) (.branch 22 (.leaf (12)) (.branch 24 (.leaf (13)) (.leaf (14))))) (.branch 31 (.branch 28 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17)))) (.branch 33 (.leaf (18)) (.branch 35 (.leaf (19)) (.leaf (20))))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 2 (.leaf (-4)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-6))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.branch 30 (.leaf (-8)) (.leaf (-7))) (.branch 34 (.leaf (-6)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_050_812 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (5)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (6)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (5)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (2))) (.branch 30 (.leaf (0)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (1))))))))
  code := certificateD7_812
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 27 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-18)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-8)) (.leaf (-9)))),
  (.branch 10 (.leaf (0)) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 28 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-11)))),
  (.leaf (0)),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 29 (.branch 16 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.leaf (-1))]
def witnessD7_050_813 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (3))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (0))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (2))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (0))) (.branch 26 (.leaf (4)) (.leaf (0))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (3))) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_813
  counts := ![(.branch 16 (.branch 7 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 25 (.branch 20 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 27 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 34 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 11 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 8 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-18)) (.leaf (-20)))),
  (.branch 4 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 11 (.leaf (-6)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 17 (.leaf (0)) (.leaf (-19))),
  (.branch 35 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 28 (.branch 21 (.leaf (-20)) (.leaf (-19))) (.branch 35 (.leaf (-18)) (.leaf (-11)))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_050_814 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (4))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (3))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (3))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (2))) (.branch 30 (.leaf (6)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_814
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 28 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-24))),
  (.branch 30 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 32 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22)))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_050_815 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (2))) (.branch 8 (.leaf (0)) (.leaf (1))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (2))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (1))))))) (.branch 27 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (5))) (.branch 22 (.leaf (1)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (0)) (.leaf (1))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (6)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (1))))))))
  code := certificateD7_815
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 10 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 28 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 3 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 20 (.leaf (-10)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-1))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-6)) (.leaf (-7)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 32 (.branch 29 (.leaf (-12)) (.leaf (-11))) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 23 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1)),
  (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_050_816 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (6)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (5)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_816
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 28 (.branch 22 (.branch 20 (.leaf (7)) (.leaf (8))) (.branch 25 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1))),
  (.branch 14 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 8 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-4)) (.leaf (-8)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-31))),
  (.branch 23 (.leaf (0)) (.leaf (-13))),
  (.branch 32 (.leaf (0)) (.leaf (-4))),
  (.branch 14 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 32 (.leaf (-17)) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 23 (.leaf (-8)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.leaf (-31)) (.branch 7 (.leaf (-30)) (.leaf (-29)))) (.branch 10 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 11 (.leaf (-26)) (.leaf (-25))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-24)) (.leaf (-23))) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-17)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_050_817 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (1)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (0))) (.branch 30 (.leaf (4)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_817
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 25 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 8 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.branch 4 (.leaf (-1)) (.leaf (-2)))),
  (.leaf (0)),
  (.branch 15 (.leaf (0)) (.leaf (-3))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.branch 5 (.leaf (0)) (.leaf (-31))),
  (.branch 22 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 32 (.leaf (-17)) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.leaf (-31)) (.branch 7 (.leaf (-30)) (.leaf (-29)))) (.branch 10 (.branch 9 (.leaf (-28)) (.leaf (-27))) (.branch 11 (.leaf (-26)) (.leaf (-25))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-24)) (.leaf (-23))) (.branch 15 (.leaf (-22)) (.leaf (-21)))) (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.leaf (-17)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-16)) (.leaf (-15))) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_050_818 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (6)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_818
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16))))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (-6)) (.leaf (-8)))),
  (.branch 7 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 27 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 33 (.leaf (-7)) (.leaf (-4))),
  (.branch 30 (.branch 25 (.leaf (-6)) (.leaf (-5))) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 33 (.branch 19 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_050_819 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (0)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (2)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_819
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-11))),
  (.branch 16 (.leaf (0)) (.leaf (-20))),
  (.branch 34 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 33 (.leaf (-7)) (.leaf (-4))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 21 (.branch 18 (.branch 17 (.leaf (-20)) (.leaf (-19))) (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16))))) (.branch 23 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6))))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_050_820 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (6))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (3)) (.branch 35 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_820
  counts := ![(.branch 17 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 11 (.branch 9 (.leaf (4)) (.leaf (5))) (.branch 13 (.leaf (6)) (.branch 15 (.leaf (7)) (.leaf (8)))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 23 (.leaf (11)) (.branch 25 (.leaf (12)) (.leaf (13))))) (.branch 31 (.branch 29 (.leaf (14)) (.leaf (15))) (.branch 33 (.leaf (16)) (.branch 35 (.leaf (17)) (.leaf (18))))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 10 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.leaf (-1)),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1))),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_050_821 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (0)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (0)) (.leaf (4))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (0)) (.leaf (6)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_821
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 12 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 14 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (8)) (.leaf (9))) (.branch 23 (.leaf (10)) (.leaf (11)))) (.branch 30 (.branch 28 (.leaf (12)) (.leaf (13))) (.branch 32 (.leaf (14)) (.branch 35 (.leaf (15)) (.leaf (16))))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-6)) (.leaf (-7)))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-23))),
  (.branch 31 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 33 (.leaf (-7)) (.leaf (-4))),
  (.branch 34 (.leaf (-6)) (.branch 35 (.leaf (-4)) (.leaf (-2)))),
  (.branch 28 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (0)),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 14 (.leaf (-23)) (.leaf (-22))) (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19))))) (.branch 21 (.branch 19 (.leaf (-18)) (.branch 20 (.leaf (-17)) (.leaf (-16)))) (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_050_822 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (5)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (0))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (6))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (0))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (5)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_822
  counts := ![(.branch 17 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.leaf (7))))) (.branch 27 (.branch 22 (.branch 20 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (10)) (.leaf (11)))) (.branch 32 (.branch 29 (.leaf (12)) (.leaf (13))) (.branch 34 (.leaf (14)) (.leaf (15)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-7))) (.branch 5 (.leaf (-9)) (.leaf (-11)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 9 (.leaf (-2)) (.leaf (-3)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-6))),
  (.leaf (0))]
  high := ![(.branch 30 (.leaf (-11)) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.leaf (-1)),
  (.branch 30 (.branch 27 (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10)))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_050_823 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (6)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (4)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_823
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-11)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 18 (.leaf (0)) (.leaf (-4))),
  (.branch 7 (.leaf (0)) (.leaf (-29))),
  (.branch 25 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 22 (.leaf (-15)) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.branch 34 (.branch 24 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 31 (.branch 19 (.leaf (-4)) (.leaf (-3))) (.branch 32 (.leaf (-2)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 21 (.branch 14 (.branch 10 (.branch 8 (.leaf (-29)) (.branch 9 (.leaf (-28)) (.leaf (-27)))) (.branch 12 (.branch 11 (.leaf (-26)) (.leaf (-25))) (.branch 13 (.leaf (-24)) (.leaf (-23))))) (.branch 17 (.branch 15 (.leaf (-22)) (.branch 16 (.leaf (-21)) (.leaf (-20)))) (.branch 19 (.branch 18 (.leaf (-19)) (.leaf (-18))) (.branch 20 (.leaf (-17)) (.leaf (-16)))))) (.branch 28 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 26 (.branch 25 (.leaf (-12)) (.leaf (-11))) (.branch 27 (.leaf (-10)) (.leaf (-9))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_050_824 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.leaf (3)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (0))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (1)) (.leaf (5))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (1)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (5))) (.branch 30 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_824
  counts := ![(.branch 15 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 10 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 13 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (-3)) (.leaf (-5)))) (.branch 21 (.leaf (-6)) (.branch 28 (.leaf (-7)) (.leaf (-8))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-22))) (.branch 12 (.leaf (-23)) (.leaf (-24)))) (.branch 27 (.branch 22 (.leaf (-25)) (.leaf (-26))) (.branch 32 (.leaf (-27)) (.leaf (-28))))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-8))) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 5 (.leaf (0)) (.branch 13 (.leaf (-4)) (.leaf (-5)))),
  (.branch 11 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.branch 29 (.leaf (-6)) (.leaf (-7)))),
  (.branch 16 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 34 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 34 (.branch 33 (.leaf (-28)) (.leaf (-21))) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 15 (.leaf (-10)) (.leaf (-7))),
  (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 12 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 35 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_050_825 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (5)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (0)) (.leaf (3)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_825
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 32 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 8 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-22))),
  (.branch 32 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.leaf (-17)) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-10)) (.leaf (-7)))),
  (.branch 29 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 15 (.leaf (-22)) (.leaf (-21))) (.branch 17 (.leaf (-20)) (.branch 18 (.leaf (-19)) (.leaf (-18))))) (.branch 22 (.branch 20 (.leaf (-17)) (.branch 21 (.leaf (-16)) (.leaf (-15)))) (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))))) (.branch 30 (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7))))) (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_050_826 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (6)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (4)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_826
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 27 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 9 (.leaf (0)) (.leaf (-27))),
  (.branch 27 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 25 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.leaf (-7)))),
  (.branch 34 (.branch 19 (.leaf (-18)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 22 (.branch 15 (.branch 12 (.branch 10 (.leaf (-27)) (.branch 11 (.leaf (-26)) (.leaf (-25)))) (.branch 13 (.leaf (-24)) (.branch 14 (.leaf (-23)) (.leaf (-22))))) (.branch 18 (.branch 16 (.leaf (-21)) (.branch 17 (.leaf (-20)) (.leaf (-19)))) (.branch 20 (.branch 19 (.leaf (-18)) (.leaf (-17))) (.branch 21 (.leaf (-16)) (.leaf (-15)))))) (.branch 29 (.branch 25 (.branch 23 (.leaf (-14)) (.branch 24 (.leaf (-13)) (.leaf (-12)))) (.branch 27 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_050_827 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (5)) (.leaf (2)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (3)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (2)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (0))) (.branch 30 (.leaf (4)) (.leaf (1)))) (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_827
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 32 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-11))) (.branch 8 (.leaf (-15)) (.leaf (-16)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 15 (.leaf (-7)) (.branch 22 (.leaf (-9)) (.leaf (-10))))),
  (.branch 27 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-5)) (.leaf (-7)))),
  (.branch 7 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 23 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 27 (.leaf (-16)) (.branch 35 (.leaf (-14)) (.leaf (-7)))),
  (.branch 33 (.branch 23 (.leaf (-10)) (.branch 32 (.leaf (-9)) (.leaf (-8)))) (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5))))),
  (.branch 34 (.leaf (-7)) (.branch 35 (.leaf (-6)) (.leaf (-5)))),
  (.branch 26 (.leaf (-2)) (.leaf (-1))),
  (.branch 32 (.branch 6 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))),
  (.branch 24 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 30 (.branch 29 (.leaf (-8)) (.leaf (-7))) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_050_828 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (6)) (.leaf (3))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (1)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (4)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (3))) (.branch 30 (.leaf (1)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (6)) (.leaf (2))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_828
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 19 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 31 (.branch 28 (.leaf (9)) (.leaf (10))) (.branch 34 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.branch 20 (.leaf (-8)) (.leaf (-10)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 18 (.leaf (-17)) (.leaf (-18)))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 14 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 25 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 26 (.branch 21 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.leaf (-7)))),
  (.branch 34 (.branch 19 (.leaf (-18)) (.leaf (-15))) (.branch 35 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 31 (.branch 29 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 33 (.branch 32 (.leaf (-5)) (.leaf (-4))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_050_829 : CycleWitness 7 where
  length := 36
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (6)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (1))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (5)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (1)) (.leaf (0)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (0))) (.branch 30 (.leaf (6)) (.leaf (0)))) (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_829
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 29 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 13 (.leaf (-11)) (.branch 31 (.leaf (-13)) (.leaf (-14))))),
  (.branch 2 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-13)) (.leaf (-18)))),
  (.branch 14 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 28 (.leaf (-2)) (.leaf (-4)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-13))),
  (.branch 12 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 32 (.leaf (-14)) (.branch 35 (.leaf (-12)) (.leaf (-7)))),
  (.branch 34 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 11 (.leaf (-18)) (.leaf (-17))) (.branch 34 (.leaf (-13)) (.branch 35 (.leaf (-9)) (.leaf (-5))))),
  (.branch 29 (.leaf (-4)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 29 (.branch 26 (.branch 24 (.leaf (-13)) (.branch 25 (.leaf (-12)) (.leaf (-11)))) (.branch 27 (.leaf (-10)) (.branch 28 (.leaf (-9)) (.leaf (-8))))) (.branch 32 (.branch 30 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))) (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 31 (.leaf (-6)) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 34 (.leaf (-3)) (.branch 35 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_050 : Fin 27 → CycleWitness 7 := ![witnessD7_050_803, witnessD7_050_804, witnessD7_050_805, witnessD7_050_806, witnessD7_050_807, witnessD7_050_808, witnessD7_050_809, witnessD7_050_810, witnessD7_050_811, witnessD7_050_812, witnessD7_050_813, witnessD7_050_814, witnessD7_050_815, witnessD7_050_816, witnessD7_050_817, witnessD7_050_818, witnessD7_050_819, witnessD7_050_820, witnessD7_050_821, witnessD7_050_822, witnessD7_050_823, witnessD7_050_824, witnessD7_050_825, witnessD7_050_826, witnessD7_050_827, witnessD7_050_828, witnessD7_050_829]
end RealPinwheel.FiveSixths


