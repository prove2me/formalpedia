-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_217
-- name    : RealPinwheel_FiveSixths_WitnessD8_217
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:00:17.272318+00:00
-- url     : https://prove2.me/theorems/342b47e3-5ecb-4ff7-80bd-ae21b020c869
-- title:
--   Exact witness block D8_217
-- statement:
--   These exact witnesses represent words 2645 through 2670 of source certificate file D8. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2645–2670; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D8.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD8
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD8_217_2644 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (1)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (1)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (0))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (1)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (7))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2644
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 10 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 29 (.leaf (-6)) (.leaf (-7)))),
  (.branch 12 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.leaf (-24))),
  (.branch 33 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 31 (.branch 21 (.leaf (-15)) (.branch 26 (.leaf (-14)) (.leaf (-13)))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-5)) (.leaf (-4)))),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22)))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_217_2645 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (7))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (6)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (7))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (4)) (.leaf (3))))))))
  code := certificateD8_2645
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-31))) (.branch 22 (.leaf (-34)) (.leaf (-36)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 10 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 35 (.branch 23 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-28)))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 15 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 31 (.leaf (-5)) (.leaf (-3))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_217_2646 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (5)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (7))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (1)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (0))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (4)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (5)) (.leaf (6))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_2646
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 31 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.leaf (-6))) (.branch 31 (.leaf (-7)) (.leaf (-9)))),
  (.branch 7 (.leaf (0)) (.branch 12 (.leaf (-1)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0))]
  high := ![(.branch 31 (.branch 21 (.leaf (-15)) (.branch 26 (.leaf (-14)) (.leaf (-13)))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7)))) (.branch 36 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.branch 35 (.branch 33 (.leaf (-12)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 35 (.branch 34 (.leaf (-10)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD8_217_2647 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (4))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (3)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (4)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (5)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (5))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (4)) (.leaf (3))))))))
  code := certificateD8_2647
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-31))) (.branch 22 (.leaf (-34)) (.leaf (-36)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (-2))) (.branch 35 (.leaf (-8)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-34))),
  (.branch 23 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 35 (.branch 23 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-28)))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 15 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 31 (.leaf (-5)) (.leaf (-3))),
  (.branch 36 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-11)))),
  (.branch 21 (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-34)) (.leaf (-33))) (.branch 7 (.leaf (-32)) (.leaf (-31)))) (.branch 10 (.branch 9 (.leaf (-30)) (.leaf (-29))) (.branch 11 (.leaf (-28)) (.leaf (-27))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-26)) (.leaf (-25))) (.branch 15 (.leaf (-24)) (.leaf (-23)))) (.branch 18 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18))))))) (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-17)) (.leaf (-16))) (.branch 24 (.leaf (-15)) (.leaf (-14)))) (.branch 27 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 28 (.leaf (-11)) (.leaf (-10))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_217_2648 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (1)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (0))) (.branch 26 (.leaf (7)) (.branch 27 (.leaf (1)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (1)) (.leaf (4))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2648
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-3)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 26 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 31 (.branch 21 (.leaf (-15)) (.branch 26 (.leaf (-14)) (.leaf (-13)))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.leaf (-6)) (.branch 33 (.leaf (-5)) (.leaf (-4)))),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.branch 23 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 35 (.branch 34 (.leaf (-10)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 22 (.branch 14 (.branch 10 (.branch 8 (.leaf (-31)) (.branch 9 (.leaf (-30)) (.leaf (-29)))) (.branch 12 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 13 (.leaf (-26)) (.leaf (-25))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-17)))))) (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_217_2649 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (7)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (1)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (0))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (7)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (3))) (.branch 36 (.leaf (5)) (.branch 37 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2649
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 10 (.leaf (-15)) (.leaf (-17)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 31 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.branch 22 (.leaf (-1)) (.leaf (-2)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 13 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 35 (.branch 30 (.leaf (-17)) (.leaf (-16))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 32 (.leaf (-4)) (.leaf (-3))),
  (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.branch 27 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.leaf (-2)) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.leaf (-2)) (.leaf (-1))),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_217_2650 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (3)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (0))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (3))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (6)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (7)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (5))) (.branch 22 (.leaf (0)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (6)) (.branch 27 (.leaf (3)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (7)) (.leaf (1))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (3))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (4)) (.leaf (6))))))))
  code := certificateD8_2650
  counts := ![(.branch 17 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 6 (.branch 1 (.leaf (0)) (.leaf (-31))) (.branch 22 (.leaf (-34)) (.leaf (-36)))),
  (.branch 9 (.branch 4 (.leaf (0)) (.leaf (-3))) (.branch 14 (.leaf (-4)) (.branch 30 (.leaf (-5)) (.leaf (-6))))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-23)) (.leaf (-29)))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 7 (.leaf (0)) (.branch 37 (.leaf (-3)) (.leaf (-7)))),
  (.branch 8 (.leaf (0)) (.leaf (-14))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.branch 29 (.leaf (-8)) (.leaf (-10))))]
  high := ![(.branch 35 (.branch 23 (.leaf (-36)) (.branch 34 (.leaf (-35)) (.leaf (-28)))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 31 (.leaf (-6)) (.branch 37 (.leaf (-5)) (.leaf (-3)))),
  (.branch 34 (.branch 25 (.branch 17 (.leaf (-29)) (.leaf (-28))) (.branch 33 (.leaf (-27)) (.leaf (-23)))) (.branch 36 (.branch 35 (.leaf (-19)) (.leaf (-15))) (.branch 37 (.leaf (-11)) (.leaf (-7))))),
  (.branch 20 (.branch 4 (.leaf (-19)) (.branch 12 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 28 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-11)) (.leaf (-7))))),
  (.leaf (-7)),
  (.branch 35 (.branch 9 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-7)))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_217_2651 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (0)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (2))) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (2)) (.leaf (5)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (1)) (.leaf (4))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2651
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 6 (.branch 3 (.leaf (0)) (.leaf (-9))) (.branch 25 (.leaf (-18)) (.leaf (-25)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.leaf (-26))),
  (.branch 31 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 30 (.branch 24 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-5)) (.leaf (-3))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 35 (.branch 28 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 37 (.leaf (-6)) (.leaf (-3))),
  (.branch 35 (.branch 26 (.leaf (-25)) (.branch 34 (.leaf (-24)) (.leaf (-22)))) (.branch 36 (.leaf (-20)) (.branch 37 (.leaf (-18)) (.leaf (-16))))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 25 (.branch 18 (.branch 15 (.branch 13 (.leaf (-26)) (.branch 14 (.leaf (-25)) (.leaf (-24)))) (.branch 16 (.leaf (-23)) (.branch 17 (.leaf (-22)) (.leaf (-21))))) (.branch 21 (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18)))) (.branch 23 (.branch 22 (.leaf (-17)) (.leaf (-16))) (.branch 24 (.leaf (-15)) (.leaf (-14)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_217_2652 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (1))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (7)) (.leaf (1))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (5)) (.leaf (6))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (2))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (5)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (6)) (.leaf (1))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (7)) (.leaf (1))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (5)) (.leaf (6))))))))
  code := certificateD8_2652
  counts := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4)))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-7)) (.leaf (-8)))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-28)) (.leaf (-31)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 28 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 8 (.leaf (0)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 5 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 35 (.branch 27 (.leaf (-17)) (.branch 34 (.leaf (-15)) (.leaf (-12)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 34 (.branch 10 (.leaf (-31)) (.branch 33 (.leaf (-30)) (.leaf (-25)))) (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-15))) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 29 (.leaf (-12)) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 32 (.leaf (-14)) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.leaf (-3)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 35 (.branch 25 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2)))))]
def witnessD8_217_2653 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (0))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (7)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (0))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (1)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (4)) (.leaf (7))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (6))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (4)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (7)) (.branch 32 (.leaf (2)) (.leaf (5))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (4))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_2653
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 34 (.leaf (-23)) (.leaf (-28)))),
  (.branch 5 (.leaf (0)) (.branch 20 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.branch 2 (.leaf (0)) (.leaf (-28))) (.branch 24 (.leaf (-31)) (.leaf (-32)))),
  (.branch 22 (.branch 7 (.leaf (0)) (.leaf (-2))) (.branch 29 (.leaf (-3)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-6))) (.branch 31 (.leaf (-9)) (.leaf (-11))))]
  high := ![(.branch 36 (.branch 35 (.leaf (-28)) (.leaf (-22))) (.branch 37 (.leaf (-16)) (.leaf (-10)))),
  (.branch 29 (.branch 21 (.leaf (-14)) (.leaf (-12))) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 25 (.leaf (-32)) (.branch 33 (.leaf (-30)) (.leaf (-25)))) (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-15))) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 30 (.leaf (-5)) (.leaf (-4))),
  (.branch 36 (.branch 19 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 35 (.branch 24 (.leaf (-11)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 13 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 34 (.branch 32 (.leaf (-11)) (.branch 33 (.leaf (-10)) (.leaf (-9)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))))]
def witnessD8_217_2654 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (7)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (1)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (6)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (7)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (5)) (.leaf (0))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (1)) (.leaf (4))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (6)) (.branch 37 (.leaf (3)) (.leaf (1))))))))
  code := certificateD8_2654
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-4)) (.leaf (-5)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.leaf (-10))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-3)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 35 (.branch 24 (.leaf (-11)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-10)) (.leaf (-9))) (.branch 32 (.leaf (-8)) (.leaf (-7)))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 23 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_217_2655 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (6)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (7)) (.leaf (5))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (3)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (6))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (6)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (2))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (5)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (7)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (4))))))))
  code := certificateD8_2655
  counts := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 7 (.leaf (-16)) (.leaf (-17)))),
  (.branch 5 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.branch 9 (.leaf (-28)) (.leaf (-31)))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-8))) (.branch 28 (.leaf (-11)) (.leaf (-12)))),
  (.branch 15 (.leaf (0)) (.branch 30 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.branch 11 (.leaf (-18)) (.leaf (-21)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-9)) (.leaf (-14)))),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 35 (.branch 27 (.leaf (-17)) (.branch 34 (.leaf (-15)) (.leaf (-12)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 34 (.branch 10 (.leaf (-31)) (.branch 33 (.leaf (-30)) (.leaf (-25)))) (.branch 36 (.branch 35 (.leaf (-20)) (.leaf (-15))) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 29 (.leaf (-12)) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 31 (.leaf (-2)) (.leaf (0))),
  (.branch 35 (.branch 12 (.leaf (-21)) (.leaf (-20))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 36 (.branch 23 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.leaf (-11)))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_217_2656 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (1)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (1)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (1)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (0))) (.branch 26 (.leaf (7)) (.branch 27 (.leaf (1)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (0))) (.branch 36 (.leaf (5)) (.branch 37 (.leaf (1)) (.leaf (2))))))))
  code := certificateD8_2656
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 14 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 33 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-6))) (.branch 31 (.leaf (-8)) (.leaf (-9)))),
  (.branch 17 (.leaf (0)) (.leaf (-2))),
  (.branch 7 (.leaf (0)) (.leaf (-31))),
  (.branch 26 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 31 (.branch 21 (.leaf (-15)) (.branch 26 (.leaf (-14)) (.leaf (-13)))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 28 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-5)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-10))) (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4))))),
  (.branch 34 (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7)))) (.branch 36 (.branch 35 (.leaf (-6)) (.leaf (-5))) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 37 (.leaf (-2)) (.leaf (-1))),
  (.branch 22 (.branch 14 (.branch 10 (.branch 8 (.leaf (-31)) (.branch 9 (.leaf (-30)) (.leaf (-29)))) (.branch 12 (.branch 11 (.leaf (-28)) (.leaf (-27))) (.branch 13 (.leaf (-26)) (.leaf (-25))))) (.branch 18 (.branch 16 (.branch 15 (.leaf (-24)) (.leaf (-23))) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 20 (.branch 19 (.leaf (-20)) (.leaf (-19))) (.branch 21 (.leaf (-18)) (.leaf (-17)))))) (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_217_2657 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (2)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (2)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (2)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (6))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (1))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (7))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (2)) (.leaf (1))))))))
  code := certificateD8_2657
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 11 (.leaf (0)) (.leaf (-8))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-22))),
  (.branch 35 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 35 (.branch 25 (.leaf (-18)) (.branch 30 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 29 (.branch 24 (.leaf (-3)) (.leaf (-2))) (.branch 34 (.leaf (-1)) (.leaf (0)))),
  (.branch 28 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-5)) (.leaf (-4)))),
  (.branch 27 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 21 (.branch 18 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18))))) (.branch 24 (.branch 22 (.leaf (-17)) (.branch 23 (.leaf (-16)) (.leaf (-15)))) (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD8_217_2658 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (2))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (4))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (7))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (5))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (2)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (3))) (.branch 22 (.leaf (5)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (2))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (4)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (5))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (7))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (2)) (.leaf (5))))))))
  code := certificateD8_2658
  counts := ![(.branch 13 (.branch 1 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 35 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 13 (.leaf (-17)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.leaf (-19))),
  (.branch 22 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-14))),
  (.branch 14 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 35 (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-15)) (.leaf (-12)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 20 (.branch 4 (.leaf (-19)) (.branch 12 (.leaf (-18)) (.leaf (-17)))) (.branch 36 (.branch 28 (.leaf (-16)) (.leaf (-15))) (.branch 37 (.leaf (-11)) (.leaf (-7))))),
  (.branch 23 (.leaf (-5)) (.branch 31 (.leaf (-4)) (.leaf (0)))),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_217_2659 : CycleWitness 8 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (7)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (4)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (2))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (5)) (.leaf (1))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 22 (.leaf (7)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (3))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (5)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (4)) (.leaf (2))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (2))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (5)) (.leaf (1))))))))
  code := certificateD8_2659
  counts := ![(.branch 14 (.branch 1 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.branch 31 (.leaf (-2)) (.leaf (-3)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-5))) (.branch 35 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.branch 2 (.leaf (0)) (.leaf (-28))) (.branch 32 (.leaf (-29)) (.leaf (-30)))),
  (.branch 6 (.leaf (0)) (.branch 13 (.leaf (-8)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.branch 18 (.leaf (-1)) (.leaf (-2)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 35 (.branch 21 (.leaf (-16)) (.branch 34 (.leaf (-15)) (.leaf (-12)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 35 (.branch 33 (.leaf (-30)) (.branch 34 (.leaf (-25)) (.leaf (-20)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (-2)),
  (.branch 35 (.branch 25 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_217_2660 : CycleWitness 8 where
  length := 37
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (3)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (7)) (.leaf (1)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (3)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (0))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (1)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (7)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (3)) (.leaf (4)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (2))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (0)) (.leaf (5))))))))
  code := certificateD8_2660
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 21 (.leaf (-18)) (.leaf (-21)))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-14)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 31 (.leaf (-17)) (.leaf (-19)))),
  (.branch 7 (.leaf (0)) (.leaf (-16))),
  (.branch 18 (.leaf (0)) (.leaf (-1))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.branch 26 (.leaf (-10)) (.leaf (-12))))]
  high := ![(.branch 28 (.branch 22 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19)))) (.branch 31 (.leaf (-18)) (.branch 34 (.leaf (-17)) (.leaf (-16))))),
  (.branch 29 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 36 (.leaf (-11)) (.leaf (-6)))),
  (.branch 35 (.branch 16 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-16)) (.leaf (-13)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-7)) (.leaf (-4))))),
  (.branch 34 (.branch 8 (.leaf (-16)) (.branch 33 (.leaf (-15)) (.leaf (-12)))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 19 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.leaf (-2))))),
  (.branch 31 (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 35 (.leaf (-4)) (.branch 36 (.leaf (-3)) (.leaf (-2))))))]
def witnessD8_217_2661 : CycleWitness 8 where
  length := 37
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (2))) (.branch 4 (.leaf (1)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (1)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (5)) (.leaf (2))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (0))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (7)) (.leaf (0))) (.branch 31 (.leaf (1)) (.leaf (3)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (5))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (0)) (.leaf (1))))))))
  code := certificateD8_2661
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 9 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 21 (.leaf (-18)) (.leaf (-21)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-1))) (.branch 26 (.leaf (-2)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 7 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.leaf (-25))),
  (.branch 15 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-25))),
  (.branch 29 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 28 (.branch 22 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19)))) (.branch 31 (.leaf (-18)) (.branch 34 (.leaf (-17)) (.leaf (-16))))),
  (.branch 33 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 34 (.leaf (-2)) (.branch 35 (.leaf (-1)) (.leaf (0))))),
  (.branch 29 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 36 (.leaf (-11)) (.leaf (-6)))),
  (.branch 34 (.branch 8 (.leaf (-16)) (.branch 33 (.leaf (-15)) (.leaf (-12)))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.branch 27 (.branch 7 (.leaf (-25)) (.branch 26 (.leaf (-24)) (.leaf (-22)))) (.branch 28 (.leaf (-20)) (.branch 29 (.leaf (-18)) (.leaf (-16))))) (.branch 33 (.branch 31 (.leaf (-14)) (.branch 32 (.leaf (-12)) (.leaf (-10)))) (.branch 35 (.branch 34 (.leaf (-8)) (.leaf (-6))) (.branch 36 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 35 (.branch 16 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 18 (.branch 15 (.branch 13 (.leaf (-25)) (.branch 14 (.leaf (-24)) (.leaf (-23)))) (.branch 16 (.leaf (-22)) (.branch 17 (.leaf (-21)) (.leaf (-20))))) (.branch 21 (.branch 19 (.leaf (-19)) (.branch 20 (.leaf (-18)) (.leaf (-17)))) (.branch 22 (.leaf (-16)) (.branch 23 (.leaf (-15)) (.leaf (-14)))))) (.branch 30 (.branch 27 (.branch 25 (.leaf (-13)) (.branch 26 (.leaf (-12)) (.leaf (-11)))) (.branch 28 (.leaf (-10)) (.branch 29 (.leaf (-9)) (.leaf (-8))))) (.branch 33 (.branch 31 (.leaf (-7)) (.branch 32 (.leaf (-6)) (.leaf (-5)))) (.branch 35 (.branch 34 (.leaf (-4)) (.leaf (-3))) (.branch 36 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-8)) (.leaf (-7))) (.branch 32 (.leaf (-6)) (.leaf (-5)))) (.branch 35 (.branch 34 (.leaf (-4)) (.leaf (-3))) (.branch 36 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_217_2662 : CycleWitness 8 where
  length := 37
  word := (.branch 19 (.branch 10 (.branch 5 (.branch 3 (.branch 2 (.leaf (0)) (.leaf (5))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (3)) (.leaf (6)))))) (.branch 14 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (7))) (.branch 13 (.leaf (2)) (.leaf (0)))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (5))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (0))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (4)) (.leaf (0))) (.branch 22 (.leaf (6)) (.leaf (2)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (5)))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (7)) (.leaf (0))) (.branch 31 (.leaf (2)) (.leaf (4)))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (6)) (.branch 36 (.leaf (0)) (.leaf (3))))))))
  code := certificateD8_2662
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 27 (.branch 21 (.branch 19 (.leaf (7)) (.leaf (8))) (.branch 24 (.leaf (9)) (.leaf (10)))) (.branch 33 (.branch 30 (.leaf (11)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14)))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 2 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 21 (.leaf (-18)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-14)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 31 (.leaf (-17)) (.leaf (-19)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 26 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-16))),
  (.branch 3 (.leaf (0)) (.leaf (-28))),
  (.branch 10 (.leaf (0)) (.branch 22 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 28 (.branch 22 (.leaf (-21)) (.branch 25 (.leaf (-20)) (.leaf (-19)))) (.branch 31 (.leaf (-18)) (.branch 34 (.leaf (-17)) (.leaf (-16))))),
  (.branch 35 (.branch 16 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-16)) (.leaf (-13)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-7)) (.leaf (-4))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))),
  (.branch 34 (.branch 8 (.leaf (-16)) (.branch 33 (.leaf (-15)) (.leaf (-12)))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.branch 29 (.branch 4 (.leaf (-28)) (.leaf (-27))) (.branch 30 (.leaf (-24)) (.branch 31 (.leaf (-21)) (.leaf (-18))))) (.branch 34 (.branch 33 (.leaf (-15)) (.leaf (-12))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 23 (.leaf (-8)) (.branch 36 (.leaf (-6)) (.leaf (-3)))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.leaf (-2)))))]
def witnessD8_217_2663 : CycleWitness 8 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (6))) (.branch 12 (.leaf (2)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (2))) (.branch 21 (.leaf (0)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (5)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (6))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (1)) (.leaf (0))))) (.branch 34 (.branch 33 (.leaf (3)) (.leaf (2))) (.branch 35 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (7))))))))
  code := certificateD8_2663
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 32 (.leaf (9)) (.branch 35 (.leaf (10)) (.leaf (11)))))),
  (.branch 16 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 10 (.leaf (-21)) (.branch 13 (.leaf (-22)) (.leaf (-25))))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 25 (.leaf (-12)) (.leaf (-16)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.branch 23 (.leaf (-13)) (.leaf (-15)))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (-19))) (.branch 30 (.leaf (-20)) (.leaf (-21)))),
  (.branch 9 (.leaf (0)) (.branch 27 (.leaf (-19)) (.leaf (-20)))),
  (.branch 11 (.leaf (0)) (.branch 29 (.leaf (-15)) (.leaf (-16)))),
  (.leaf (0))]
  high := ![(.branch 25 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 36 (.leaf (-23)) (.leaf (-18)))),
  (.leaf (-16)),
  (.branch 35 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 36 (.leaf (-5)) (.leaf (-3)))),
  (.branch 34 (.branch 24 (.leaf (-15)) (.leaf (-13))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-7)) (.leaf (-4))))),
  (.branch 33 (.branch 31 (.leaf (-21)) (.branch 32 (.leaf (-18)) (.leaf (-15)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-9))) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-20)) (.leaf (-18))) (.branch 30 (.leaf (-16)) (.branch 31 (.leaf (-14)) (.leaf (-12))))) (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-8))) (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-4)) (.leaf (-2)))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-16)) (.leaf (-14))) (.branch 32 (.leaf (-12)) (.leaf (-10)))) (.branch 35 (.branch 34 (.leaf (-8)) (.leaf (-6))) (.branch 36 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0))]
def witnessD8_217_2664 : CycleWitness 8 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (3)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.leaf (5)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (4)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (7)) (.leaf (0))) (.branch 25 (.leaf (1)) (.branch 26 (.leaf (2)) (.leaf (3)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (0)) (.leaf (5))))) (.branch 34 (.branch 33 (.leaf (2)) (.leaf (0))) (.branch 35 (.leaf (1)) (.branch 36 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_2664
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 31 (.leaf (9)) (.branch 34 (.leaf (10)) (.leaf (11)))))),
  (.branch 16 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 22 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-17)) (.leaf (-27)))),
  (.branch 16 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 20 (.leaf (-4)) (.branch 29 (.leaf (-5)) (.leaf (-6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.branch 36 (.leaf (-3)) (.leaf (-4))))),
  (.branch 6 (.leaf (0)) (.branch 30 (.leaf (-13)) (.leaf (-15)))),
  (.branch 13 (.leaf (0)) (.leaf (-11))),
  (.branch 4 (.leaf (0)) (.leaf (-33))),
  (.branch 23 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 35 (.branch 4 (.leaf (-27)) (.leaf (-26))) (.branch 36 (.leaf (-19)) (.leaf (-12)))),
  (.branch 30 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4)))),
  (.branch 34 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-4)),
  (.branch 33 (.branch 31 (.leaf (-15)) (.branch 32 (.leaf (-13)) (.leaf (-11)))) (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-7))) (.branch 36 (.leaf (-5)) (.leaf (-3))))),
  (.branch 34 (.branch 14 (.leaf (-11)) (.branch 33 (.leaf (-10)) (.leaf (-8)))) (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-4)) (.leaf (-2))))),
  (.branch 20 (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-33)) (.leaf (-32))) (.branch 7 (.leaf (-31)) (.leaf (-30)))) (.branch 10 (.branch 9 (.leaf (-29)) (.leaf (-28))) (.branch 11 (.leaf (-27)) (.leaf (-26))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-25)) (.leaf (-24))) (.branch 15 (.leaf (-23)) (.leaf (-22)))) (.branch 18 (.branch 17 (.leaf (-21)) (.leaf (-20))) (.branch 19 (.leaf (-19)) (.leaf (-18)))))) (.branch 28 (.branch 24 (.branch 22 (.branch 21 (.leaf (-17)) (.leaf (-16))) (.branch 23 (.leaf (-15)) (.leaf (-14)))) (.branch 26 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 27 (.leaf (-11)) (.leaf (-10))))) (.branch 32 (.branch 30 (.branch 29 (.leaf (-9)) (.leaf (-8))) (.branch 31 (.leaf (-7)) (.leaf (-6)))) (.branch 34 (.branch 33 (.leaf (-5)) (.leaf (-4))) (.branch 35 (.leaf (-3)) (.branch 36 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 28 (.branch 27 (.leaf (-11)) (.leaf (-10))) (.branch 29 (.leaf (-9)) (.leaf (-8))))) (.branch 33 (.branch 31 (.leaf (-7)) (.branch 32 (.leaf (-6)) (.leaf (-5)))) (.branch 35 (.branch 34 (.leaf (-4)) (.leaf (-3))) (.branch 36 (.leaf (-2)) (.leaf (-1))))))]
def witnessD8_217_2665 : CycleWitness 8 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (6))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (3)) (.leaf (7))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (4)) (.leaf (2))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (3)))) (.branch 24 (.branch 23 (.leaf (6)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (0)) (.leaf (1)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (3)) (.leaf (0))) (.branch 30 (.leaf (4)) (.branch 31 (.leaf (5)) (.leaf (2))))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (7)) (.branch 36 (.leaf (3)) (.leaf (6))))))))
  code := certificateD8_2665
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-10)))) (.branch 16 (.leaf (-12)) (.branch 29 (.leaf (-13)) (.leaf (-14))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 24 (.leaf (-12)) (.branch 27 (.leaf (-13)) (.leaf (-21))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-22))) (.branch 32 (.leaf (-24)) (.leaf (-25)))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.branch 17 (.leaf (-22)) (.leaf (-23)))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (-11)) (.leaf (-13)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (-2)) (.leaf (-3)))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 35 (.branch 30 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-11)) (.leaf (-9)))),
  (.branch 34 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 35 (.leaf (-17)) (.branch 36 (.leaf (-14)) (.leaf (-11))))),
  (.branch 34 (.branch 33 (.leaf (-25)) (.leaf (-20))) (.branch 35 (.leaf (-15)) (.branch 36 (.leaf (-10)) (.leaf (-5))))),
  (.branch 29 (.leaf (-4)) (.leaf (-3))),
  (.branch 33 (.branch 31 (.branch 18 (.leaf (-23)) (.leaf (-21))) (.branch 32 (.leaf (-18)) (.leaf (-15)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-9))) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-11)) (.leaf (-9)))) (.branch 35 (.leaf (-7)) (.branch 36 (.leaf (-5)) (.leaf (-3))))),
  (.branch 25 (.branch 24 (.leaf (-3)) (.leaf (-2))) (.branch 26 (.leaf (-1)) (.leaf (0)))),
  (.branch 16 (.leaf (-4)) (.branch 36 (.leaf (-3)) (.leaf (-2))))]
def witnessD8_217_2666 : CycleWitness 8 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (3))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (4))) (.branch 12 (.leaf (7)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (6))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (5)) (.leaf (1))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (7))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (1)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (0))) (.branch 30 (.leaf (6)) (.branch 31 (.leaf (5)) (.leaf (1))))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (4)) (.leaf (7))))))))
  code := certificateD8_2666
  counts := ![(.branch 17 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-16))) (.branch 29 (.leaf (-22)) (.branch 33 (.leaf (-23)) (.leaf (-24))))),
  (.branch 14 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (-21)) (.leaf (-22)))) (.branch 20 (.leaf (-23)) (.branch 32 (.leaf (-24)) (.leaf (-26))))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-14)))),
  (.branch 11 (.leaf (0)) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (-16))) (.branch 31 (.leaf (-17)) (.leaf (-18)))),
  (.branch 5 (.leaf (0)) (.leaf (-22))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-1)) (.leaf (-2))))]
  high := ![(.branch 35 (.branch 34 (.leaf (-24)) (.leaf (-19))) (.branch 36 (.leaf (-14)) (.leaf (-9)))),
  (.branch 34 (.branch 33 (.leaf (-26)) (.leaf (-21))) (.branch 35 (.leaf (-16)) (.branch 36 (.leaf (-11)) (.leaf (-6))))),
  (.branch 29 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 36 (.leaf (-11)) (.leaf (-6)))),
  (.branch 35 (.branch 16 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-8)) (.leaf (-4)))),
  (.branch 24 (.leaf (-5)) (.leaf (-3))),
  (.branch 34 (.branch 32 (.leaf (-18)) (.branch 33 (.leaf (-15)) (.leaf (-12)))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.branch 31 (.branch 6 (.leaf (-22)) (.leaf (-21))) (.branch 32 (.leaf (-18)) (.leaf (-15)))) (.branch 35 (.branch 34 (.leaf (-12)) (.leaf (-9))) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.leaf (-2)) (.leaf (0)))]
def witnessD8_217_2667 : CycleWitness 8 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.leaf (6)))) (.branch 15 (.branch 14 (.leaf (0)) (.leaf (2))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (3)) (.leaf (1))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (0)) (.leaf (2))) (.branch 21 (.leaf (5)) (.leaf (1)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (0))) (.branch 25 (.leaf (2)) (.branch 26 (.leaf (4)) (.leaf (0)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (1)) (.leaf (3))) (.branch 30 (.leaf (7)) (.branch 31 (.leaf (2)) (.leaf (0))))) (.branch 34 (.branch 33 (.leaf (5)) (.leaf (1))) (.branch 35 (.leaf (4)) (.branch 36 (.leaf (3)) (.leaf (2))))))))
  code := certificateD8_2667
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-4))) (.branch 14 (.leaf (-5)) (.branch 27 (.leaf (-6)) (.leaf (-8))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 22 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.leaf (-13))),
  (.branch 13 (.leaf (0)) (.leaf (-24))),
  (.branch 30 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 34 (.branch 33 (.leaf (-8)) (.leaf (-7))) (.branch 35 (.leaf (-6)) (.branch 36 (.leaf (-5)) (.leaf (-4))))),
  (.branch 29 (.branch 23 (.leaf (-11)) (.leaf (-10))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-7)) (.leaf (-5))))),
  (.branch 32 (.branch 26 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-2)) (.leaf (0)))),
  (.branch 5 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-6)))),
  (.branch 17 (.leaf (-10)) (.branch 36 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 9 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 25 (.branch 19 (.branch 16 (.branch 14 (.leaf (-24)) (.branch 15 (.leaf (-23)) (.leaf (-22)))) (.branch 17 (.leaf (-21)) (.branch 18 (.leaf (-20)) (.leaf (-19))))) (.branch 22 (.branch 20 (.leaf (-18)) (.branch 21 (.leaf (-17)) (.leaf (-16)))) (.branch 23 (.leaf (-15)) (.branch 24 (.leaf (-14)) (.leaf (-13)))))) (.branch 31 (.branch 28 (.branch 26 (.leaf (-12)) (.branch 27 (.leaf (-11)) (.leaf (-10)))) (.branch 29 (.leaf (-9)) (.branch 30 (.leaf (-8)) (.leaf (-7))))) (.branch 34 (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-5)) (.leaf (-4)))) (.branch 35 (.leaf (-3)) (.branch 36 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.leaf (-7)) (.branch 32 (.leaf (-6)) (.leaf (-5)))) (.branch 35 (.branch 34 (.leaf (-4)) (.leaf (-3))) (.branch 36 (.leaf (-2)) (.leaf (-1)))))]
def witnessD8_217_2668 : CycleWitness 8 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (7)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (3))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (5))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (6))) (.branch 21 (.leaf (0)) (.leaf (2)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (5)) (.leaf (0)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (2)) (.leaf (7))) (.branch 30 (.leaf (1)) (.branch 31 (.leaf (4)) (.leaf (6))))) (.branch 34 (.branch 33 (.leaf (0)) (.leaf (3))) (.branch 35 (.leaf (2)) (.branch 36 (.leaf (1)) (.leaf (5))))))))
  code := certificateD8_2668
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 21 (.leaf (-12)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 3 (.leaf (0)) (.leaf (-16))),
  (.branch 6 (.leaf (0)) (.branch 15 (.leaf (-13)) (.leaf (-14)))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (-16))) (.branch 31 (.leaf (-17)) (.leaf (-19)))),
  (.branch 18 (.branch 9 (.leaf (0)) (.leaf (-1))) (.branch 26 (.leaf (-2)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (-7)) (.leaf (-9))))]
  high := ![(.branch 34 (.branch 22 (.leaf (-13)) (.branch 28 (.leaf (-12)) (.leaf (-11)))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-7)) (.leaf (-5))))),
  (.branch 25 (.leaf (-7)) (.branch 31 (.leaf (-6)) (.leaf (-5)))),
  (.branch 29 (.branch 4 (.leaf (-16)) (.leaf (-15))) (.branch 36 (.leaf (-11)) (.leaf (-6)))),
  (.branch 35 (.branch 16 (.leaf (-14)) (.leaf (-12))) (.branch 36 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 32 (.leaf (-19)) (.branch 33 (.leaf (-16)) (.leaf (-13)))) (.branch 35 (.leaf (-10)) (.branch 36 (.leaf (-7)) (.leaf (-4))))),
  (.branch 28 (.branch 27 (.leaf (-4)) (.leaf (-3))) (.branch 29 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0))))),
  (.branch 34 (.branch 8 (.leaf (-16)) (.branch 33 (.leaf (-15)) (.leaf (-12)))) (.branch 35 (.leaf (-9)) (.branch 36 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.leaf (-2)))))]
def witnessD8_217_2669 : CycleWitness 8 where
  length := 37
  word := (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (0)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (2))) (.branch 12 (.leaf (0)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (4)) (.leaf (6))) (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (3))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (1)) (.leaf (5))) (.branch 21 (.leaf (0)) (.leaf (4)))) (.branch 24 (.branch 23 (.leaf (2)) (.leaf (1))) (.branch 25 (.leaf (3)) (.branch 26 (.leaf (0)) (.leaf (1)))))) (.branch 32 (.branch 29 (.branch 28 (.leaf (4)) (.leaf (0))) (.branch 30 (.leaf (2)) (.branch 31 (.leaf (5)) (.leaf (3))))) (.branch 34 (.branch 33 (.leaf (1)) (.leaf (0))) (.branch 35 (.leaf (7)) (.branch 36 (.leaf (4)) (.leaf (2))))))))
  code := certificateD8_2669
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 34 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 36 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.leaf (1))),
  (.branch 35 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-7)) (.leaf (-10)))) (.branch 16 (.leaf (-12)) (.branch 29 (.leaf (-13)) (.leaf (-14))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 24 (.leaf (-12)) (.branch 27 (.leaf (-13)) (.leaf (-21))))),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-3))) (.branch 17 (.leaf (-4)) (.branch 23 (.leaf (-5)) (.leaf (-6))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-22))) (.branch 32 (.leaf (-24)) (.leaf (-25)))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.branch 31 (.leaf (-11)) (.leaf (-13)))),
  (.branch 15 (.leaf (0)) (.leaf (-22))),
  (.branch 35 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 35 (.branch 30 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-11)) (.leaf (-9)))),
  (.branch 34 (.branch 28 (.leaf (-21)) (.leaf (-20))) (.branch 35 (.leaf (-17)) (.branch 36 (.leaf (-14)) (.leaf (-11))))),
  (.branch 31 (.branch 24 (.leaf (-6)) (.leaf (-5))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 34 (.branch 33 (.leaf (-25)) (.leaf (-20))) (.branch 35 (.leaf (-15)) (.branch 36 (.leaf (-10)) (.leaf (-5))))),
  (.branch 29 (.leaf (-4)) (.leaf (-3))),
  (.branch 34 (.branch 32 (.leaf (-13)) (.branch 33 (.leaf (-11)) (.leaf (-9)))) (.branch 35 (.leaf (-7)) (.branch 36 (.leaf (-5)) (.leaf (-3))))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 16 (.leaf (-22)) (.leaf (-21))) (.branch 18 (.leaf (-20)) (.branch 19 (.leaf (-19)) (.leaf (-18))))) (.branch 23 (.branch 21 (.leaf (-17)) (.branch 22 (.leaf (-16)) (.leaf (-15)))) (.branch 24 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))))) (.branch 31 (.branch 28 (.branch 27 (.leaf (-11)) (.leaf (-10))) (.branch 29 (.leaf (-9)) (.branch 30 (.leaf (-8)) (.leaf (-7))))) (.branch 34 (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-5)) (.leaf (-4)))) (.branch 35 (.leaf (-3)) (.branch 36 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.leaf (-2)) (.leaf (-1)))]
def witnessD8_217 : Fin 26 → CycleWitness 8 := ![witnessD8_217_2644, witnessD8_217_2645, witnessD8_217_2646, witnessD8_217_2647, witnessD8_217_2648, witnessD8_217_2649, witnessD8_217_2650, witnessD8_217_2651, witnessD8_217_2652, witnessD8_217_2653, witnessD8_217_2654, witnessD8_217_2655, witnessD8_217_2656, witnessD8_217_2657, witnessD8_217_2658, witnessD8_217_2659, witnessD8_217_2660, witnessD8_217_2661, witnessD8_217_2662, witnessD8_217_2663, witnessD8_217_2664, witnessD8_217_2665, witnessD8_217_2666, witnessD8_217_2667, witnessD8_217_2668, witnessD8_217_2669]
end RealPinwheel.FiveSixths


