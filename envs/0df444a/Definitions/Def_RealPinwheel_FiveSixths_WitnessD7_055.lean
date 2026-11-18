-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_055
-- name    : RealPinwheel_FiveSixths_WitnessD7_055
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:03:38.73227+00:00
-- url     : https://prove2.me/theorems/ebefa492-a316-45cb-8275-64e05866d8b0
-- title:
--   Exact witness block D7_055
-- statement:
--   These exact witnesses represent words 943 through 971 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 943–971; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_055_942 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (0)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (6)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (4))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_942
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-4)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-19)) (.leaf (-23)))),
  (.branch 6 (.leaf (0)) (.branch 26 (.leaf (-4)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.leaf (-1))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 31 (.branch 30 (.leaf (-6)) (.leaf (-5))) (.branch 32 (.leaf (-4)) (.branch 33 (.leaf (-3)) (.leaf (-2))))),
  (.branch 22 (.leaf (-4)) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.branch 24 (.branch 10 (.leaf (-23)) (.branch 17 (.leaf (-22)) (.leaf (-21)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 27 (.leaf (-6)) (.leaf (-5))),
  (.branch 32 (.branch 23 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-4)) (.leaf (-2)))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_055_943 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (4))) (.branch 24 (.leaf (1)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (4)) (.leaf (2))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_943
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 14 (.leaf (-8)) (.leaf (-9)))),
  (.branch 17 (.leaf (0)) (.leaf (-1))),
  (.branch 13 (.branch 6 (.leaf (0)) (.leaf (-3))) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 5 (.leaf (0)) (.leaf (-29))),
  (.branch 22 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 29 (.branch 22 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 20 (.leaf (-7)) (.leaf (-6))),
  (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 18 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 19 (.branch 12 (.branch 8 (.branch 6 (.leaf (-29)) (.branch 7 (.leaf (-28)) (.leaf (-27)))) (.branch 10 (.branch 9 (.leaf (-26)) (.leaf (-25))) (.branch 11 (.leaf (-24)) (.leaf (-23))))) (.branch 15 (.branch 13 (.leaf (-22)) (.branch 14 (.leaf (-21)) (.leaf (-20)))) (.branch 17 (.branch 16 (.leaf (-19)) (.leaf (-18))) (.branch 18 (.leaf (-17)) (.leaf (-16)))))) (.branch 26 (.branch 22 (.branch 20 (.leaf (-15)) (.branch 21 (.leaf (-14)) (.leaf (-13)))) (.branch 24 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 25 (.leaf (-10)) (.leaf (-9))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_055_944 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 9 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 4 (.leaf (2)) (.leaf (0)))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (1))) (.branch 8 (.leaf (4)) (.leaf (0))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (3)) (.leaf (0)))) (.branch 15 (.branch 14 (.leaf (2)) (.leaf (1))) (.branch 16 (.leaf (5)) (.leaf (3)))))) (.branch 26 (.branch 22 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.leaf (0)))) (.branch 24 (.branch 23 (.leaf (3)) (.leaf (1))) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 30 (.branch 28 (.branch 27 (.leaf (2)) (.leaf (1))) (.branch 29 (.leaf (3)) (.leaf (0)))) (.branch 32 (.branch 31 (.leaf (2)) (.leaf (1))) (.branch 33 (.leaf (6)) (.leaf (3)))))))
  code := certificateD7_944
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 4 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 21 (.leaf (-6)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-9))),
  (.branch 16 (.leaf (0)) (.leaf (-18))),
  (.branch 33 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 25 (.branch 20 (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 22 (.branch 21 (.leaf (-14)) (.leaf (-13))) (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_055_945 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (2)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (6)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_945
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 32 (.leaf (8)) (.leaf (9)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 26 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-20))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-7)) (.leaf (-8)))) (.branch 18 (.leaf (-9)) (.branch 22 (.leaf (-11)) (.leaf (-12))))),
  (.branch 7 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 11 (.leaf (-5)) (.branch 19 (.leaf (-6)) (.leaf (-8))))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 26 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 2 (.leaf (-20)) (.branch 33 (.leaf (-19)) (.leaf (-12)))),
  (.branch 32 (.branch 23 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.branch 20 (.leaf (-8)) (.branch 29 (.leaf (-7)) (.leaf (-5)))),
  (.branch 31 (.branch 21 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 21 (.branch 14 (.branch 11 (.branch 9 (.leaf (-26)) (.branch 10 (.leaf (-25)) (.leaf (-24)))) (.branch 12 (.leaf (-23)) (.branch 13 (.leaf (-22)) (.leaf (-21))))) (.branch 17 (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18)))) (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-8)) (.leaf (-7))) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_055_946 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (5)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (2))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (6)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (2))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_946
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 7 (.leaf (0)) (.leaf (1))),
  (.branch 24 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-12))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 14 (.leaf (-8)) (.branch 31 (.leaf (-10)) (.leaf (-11))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.leaf (-27))),
  (.branch 24 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 26 (.branch 19 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 32 (.leaf (-11)) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 31 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 20 (.branch 13 (.branch 10 (.branch 8 (.leaf (-27)) (.branch 9 (.leaf (-26)) (.leaf (-25)))) (.branch 11 (.leaf (-24)) (.branch 12 (.leaf (-23)) (.leaf (-22))))) (.branch 16 (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19)))) (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))))) (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 26 (.branch 25 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.branch 28 (.leaf (-7)) (.leaf (-6))))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_055_947 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (0)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_947
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 29 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 21 (.leaf (2)) (.branch 30 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 4 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.branch 6 (.leaf (0)) (.leaf (-6))) (.branch 27 (.leaf (-14)) (.leaf (-21)))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 19 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))),
  (.branch 20 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.branch 28 (.leaf (-21)) (.branch 29 (.leaf (-20)) (.leaf (-19)))) (.branch 32 (.branch 31 (.leaf (-18)) (.leaf (-17))) (.branch 33 (.leaf (-16)) (.leaf (-15))))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))) (.branch 23 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-10))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_055_948 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (6)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (3))) (.branch 20 (.leaf (5)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (6)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (5))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_948
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 25 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 15 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 18 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (-7)) (.leaf (-8)))) (.branch 22 (.leaf (-9)) (.branch 25 (.leaf (-10)) (.leaf (-13))))),
  (.branch 2 (.leaf (0)) (.branch 21 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-4))) (.branch 29 (.leaf (-5)) (.leaf (-6)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 31 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-10)) (.branch 33 (.leaf (-8)) (.leaf (-6))))),
  (.branch 22 (.leaf (-4)) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.branch 31 (.branch 30 (.leaf (-6)) (.leaf (-5))) (.branch 32 (.leaf (-4)) (.branch 33 (.leaf (-3)) (.leaf (-2))))),
  (.branch 27 (.branch 5 (.leaf (-13)) (.leaf (-12))) (.branch 28 (.leaf (-8)) (.branch 29 (.leaf (-4)) (.leaf (0))))),
  (.branch 16 (.branch 7 (.leaf (-8)) (.leaf (-7))) (.branch 25 (.leaf (-6)) (.leaf (-5)))),
  (.branch 32 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_055_949 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (2)) (.leaf (1))) (.branch 20 (.leaf (0)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (5)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_949
  counts := ![(.branch 16 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 20 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 12 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 27 (.leaf (-28)) (.leaf (-29)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 25 (.branch 3 (.leaf (0)) (.leaf (-5))) (.branch 29 (.leaf (-9)) (.branch 33 (.leaf (-11)) (.leaf (-13))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-22))) (.branch 26 (.leaf (-23)) (.leaf (-24)))),
  (.leaf (0)),
  (.branch 11 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-12)) (.leaf (-15))))]
  high := ![(.branch 32 (.branch 28 (.leaf (-29)) (.leaf (-27))) (.branch 33 (.leaf (-18)) (.leaf (-9)))),
  (.branch 24 (.branch 15 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (-13)),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-24)) (.leaf (-21))) (.branch 29 (.leaf (-18)) (.leaf (-15)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 31 (.branch 12 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-15)) (.branch 23 (.leaf (-14)) (.leaf (-13)))) (.branch 25 (.leaf (-12)) (.branch 26 (.leaf (-11)) (.leaf (-10))))) (.branch 30 (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7)))) (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3))))))]
def witnessD7_055_950 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (4)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (6)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (5)) (.leaf (3))))))))
  code := certificateD7_950
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 11 (.leaf (-12)) (.leaf (-13)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 26 (.leaf (-15)) (.leaf (-17)))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 29 (.leaf (-13)) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 32 (.leaf (-12)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.branch 25 (.leaf (-3)) (.leaf (-2))) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-17)) (.leaf (-15))) (.branch 29 (.leaf (-13)) (.leaf (-11)))) (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-7))) (.branch 33 (.leaf (-5)) (.leaf (-3))))),
  (.branch 10 (.leaf (-5)) (.branch 22 (.leaf (-4)) (.leaf (-3)))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_055_951 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (5)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (2))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (4)) (.leaf (6)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (2))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_951
  counts := ![(.branch 13 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.branch 13 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 4 (.leaf (0)) (.leaf (-8))),
  (.branch 11 (.leaf (0)) (.branch 21 (.leaf (-1)) (.leaf (-3)))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 32 (.branch 31 (.leaf (-16)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 28 (.leaf (-11)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 25 (.leaf (-3)) (.leaf (-2))),
  (.branch 31 (.branch 29 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-6)))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 23 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 24 (.leaf (-1)) (.leaf (0)))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_055_952 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (6)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (3)) (.leaf (0))) (.branch 16 (.leaf (4)) (.leaf (2)))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (4)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (6)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 33 (.leaf (4)) (.leaf (3)))))))
  code := certificateD7_952
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 29 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-19)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (-1))) (.branch 33 (.leaf (-13)) (.leaf (-24)))),
  (.branch 4 (.leaf (0)) (.leaf (-13))),
  (.branch 11 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 31 (.branch 24 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.branch 28 (.leaf (-1)) (.leaf (0))))),
  (.leaf (-24)),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_055_953 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (4))) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (0))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (5))) (.branch 20 (.leaf (2)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (6)) (.leaf (1))) (.branch 24 (.leaf (3)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (5)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_953
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 28 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 31 (.leaf (-20)) (.leaf (-26)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 14 (.leaf (-8)) (.branch 18 (.leaf (-10)) (.leaf (-11))))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 7 (.leaf (0)) (.branch 15 (.leaf (-3)) (.leaf (-4)))),
  (.branch 16 (.leaf (0)) (.leaf (-2))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (-10))) (.branch 30 (.leaf (-11)) (.leaf (-12)))),
  (.branch 4 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 32 (.leaf (-26)) (.branch 33 (.leaf (-19)) (.leaf (-12)))),
  (.branch 28 (.branch 19 (.leaf (-11)) (.leaf (-10))) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 16 (.leaf (-4)) (.branch 25 (.leaf (-3)) (.leaf (-2)))),
  (.branch 17 (.leaf (-2)) (.branch 27 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 27 (.branch 24 (.branch 5 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_055_954 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (5))) (.branch 24 (.leaf (1)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.leaf (4)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (5))))))))
  code := certificateD7_954
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 30 (.leaf (-5)) (.leaf (-6)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-16)) (.leaf (-17)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 32 (.branch 23 (.leaf (-14)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.leaf (-2)),
  (.branch 31 (.branch 18 (.leaf (-17)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_055_955 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (2))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (2)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (1)) (.leaf (4))) (.branch 28 (.leaf (0)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (2))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (6))))))))
  code := certificateD7_955
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 19 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 30 (.leaf (8)) (.branch 33 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.branch 27 (.leaf (1)) (.leaf (2)))),
  (.branch 17 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-12)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.leaf (-7))),
  (.branch 7 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 24 (.leaf (-7)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-7))),
  (.branch 17 (.leaf (0)) (.leaf (-17))),
  (.leaf (0))]
  high := ![(.branch 29 (.branch 22 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 20 (.leaf (-7)) (.branch 27 (.leaf (-6)) (.leaf (-5)))),
  (.branch 32 (.leaf (-11)) (.branch 33 (.leaf (-10)) (.leaf (-9)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))) (.branch 23 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 24 (.leaf (-11)) (.leaf (-10))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_055_956 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (2)) (.leaf (4))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (6))) (.branch 24 (.leaf (1)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (4)) (.leaf (3))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_956
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 6 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 33 (.leaf (-2)) (.leaf (-3)))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.leaf (-28))),
  (.branch 23 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3)),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.leaf (0)),
  (.branch 20 (.branch 13 (.branch 9 (.branch 7 (.leaf (-28)) (.branch 8 (.leaf (-27)) (.leaf (-26)))) (.branch 11 (.branch 10 (.leaf (-25)) (.leaf (-24))) (.branch 12 (.leaf (-23)) (.leaf (-22))))) (.branch 16 (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19)))) (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))))) (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_055_957 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (4)) (.leaf (1)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (4)) (.leaf (1))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (5))) (.branch 24 (.leaf (2)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (4)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (3))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_957
  counts := ![(.branch 13 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 21 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 30 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 6 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 21 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.leaf (-20))),
  (.branch 19 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 8 (.leaf (-8)) (.leaf (-10)))),
  (.branch 16 (.leaf (0)) (.branch 33 (.leaf (-6)) (.leaf (-11)))),
  (.branch 23 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.leaf (-28)))]
  high := ![(.branch 31 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 32 (.leaf (-11)) (.branch 33 (.leaf (-8)) (.leaf (-5))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (-20)) (.leaf (-19))) (.branch 13 (.leaf (-18)) (.leaf (-17)))) (.branch 28 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-14)) (.leaf (-7))))),
  (.branch 25 (.branch 20 (.leaf (-3)) (.leaf (-2))) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 32 (.branch 26 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-11)),
  (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 20 (.branch 13 (.branch 9 (.branch 7 (.leaf (-28)) (.branch 8 (.leaf (-27)) (.leaf (-26)))) (.branch 11 (.branch 10 (.leaf (-25)) (.leaf (-24))) (.branch 12 (.leaf (-23)) (.leaf (-22))))) (.branch 16 (.branch 14 (.leaf (-21)) (.branch 15 (.leaf (-20)) (.leaf (-19)))) (.branch 18 (.branch 17 (.leaf (-18)) (.leaf (-17))) (.branch 19 (.leaf (-16)) (.leaf (-15)))))) (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_055_958 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (5)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (4)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (6)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_958
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-21))),
  (.branch 30 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 28 (.leaf (-10)) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 27 (.leaf (-4)) (.leaf (-3))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 18 (.branch 15 (.branch 14 (.leaf (-21)) (.leaf (-20))) (.branch 16 (.leaf (-19)) (.branch 17 (.leaf (-18)) (.leaf (-17))))) (.branch 20 (.branch 19 (.leaf (-16)) (.leaf (-15))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_055_959 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (0))) (.branch 11 (.leaf (1)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (0)) (.leaf (3))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (0)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (1)) (.leaf (6)))) (.branch 31 (.branch 30 (.leaf (0)) (.leaf (4))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_959
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 24 (.branch 18 (.leaf (6)) (.branch 21 (.leaf (7)) (.leaf (8)))) (.branch 30 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 33 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-11))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (-25))) (.branch 25 (.leaf (-26)) (.leaf (-27)))),
  (.branch 8 (.leaf (0)) (.leaf (-10))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 25 (.branch 19 (.leaf (-11)) (.branch 22 (.leaf (-10)) (.leaf (-9)))) (.branch 28 (.leaf (-8)) (.branch 31 (.leaf (-7)) (.leaf (-6))))),
  (.branch 24 (.leaf (-10)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-27)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 32 (.branch 9 (.leaf (-10)) (.leaf (-9))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_055_960 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (0)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (1))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (0)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (1)) (.leaf (0))) (.branch 20 (.leaf (4)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (0))) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (2)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (6)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_960
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 23 (.branch 19 (.leaf (5)) (.leaf (6))) (.branch 27 (.leaf (7)) (.branch 31 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 29 (.leaf (7)) (.branch 33 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-25))) (.branch 19 (.leaf (-32)) (.leaf (-33)))),
  (.branch 2 (.leaf (0)) (.leaf (-16))),
  (.branch 11 (.leaf (0)) (.branch 28 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-25))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-7)) (.leaf (-8)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 28 (.branch 20 (.leaf (-33)) (.branch 24 (.leaf (-31)) (.leaf (-29)))) (.branch 32 (.leaf (-27)) (.branch 33 (.leaf (-18)) (.leaf (-9))))),
  (.branch 22 (.branch 3 (.leaf (-16)) (.leaf (-15))) (.branch 26 (.leaf (-13)) (.branch 30 (.leaf (-11)) (.leaf (-9))))),
  (.branch 29 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 29 (.branch 27 (.branch 4 (.leaf (-25)) (.leaf (-24))) (.branch 28 (.leaf (-21)) (.leaf (-18)))) (.branch 31 (.branch 30 (.leaf (-15)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 21 (.leaf (-8)) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_055_961 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (6)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (5)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (0))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (6)) (.leaf (0))) (.branch 32 (.leaf (1)) (.branch 33 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_961
  counts := ![(.branch 14 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 25 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 31 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 22 (.leaf (1)) (.leaf (2)))),
  (.branch 13 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-12))) (.branch 14 (.leaf (-14)) (.leaf (-15)))),
  (.branch 10 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-9)) (.leaf (-10)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.branch 26 (.leaf (-9)) (.leaf (-10)))),
  (.branch 9 (.leaf (0)) (.branch 20 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-12))),
  (.branch 13 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.branch 28 (.leaf (-10)) (.branch 33 (.leaf (-8)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.leaf (-7)))) (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.branch 21 (.leaf (-4)) (.leaf (-3))),
  (.branch 28 (.branch 25 (.branch 23 (.leaf (-12)) (.branch 24 (.leaf (-11)) (.leaf (-10)))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_055_962 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (2)) (.branch 16 (.leaf (1)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (1)) (.leaf (2))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (4))) (.branch 28 (.leaf (1)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_962
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 28 (.leaf (6)) (.branch 33 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 4 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 23 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 27 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 29 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 19 (.leaf (-7)) (.leaf (-8)))),
  (.branch 8 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.branch 23 (.leaf (-19)) (.leaf (-21)))),
  (.branch 6 (.leaf (0)) (.leaf (-4))),
  (.branch 29 (.leaf (0)) (.leaf (-5))),
  (.branch 12 (.leaf (0)) (.leaf (-22)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 20 (.leaf (-8)) (.branch 29 (.leaf (-7)) (.leaf (-5)))),
  (.branch 26 (.leaf (-5)) (.branch 33 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.branch 24 (.leaf (-21)) (.leaf (-20))) (.branch 32 (.leaf (-15)) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 14 (.branch 7 (.leaf (-4)) (.leaf (-3))) (.branch 21 (.leaf (-2)) (.branch 28 (.leaf (-1)) (.leaf (0))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_055_963 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (2))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (1)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (0))) (.branch 15 (.leaf (6)) (.branch 16 (.leaf (1)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (3)) (.leaf (1)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (4))) (.branch 24 (.leaf (2)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (3))) (.branch 28 (.leaf (2)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (6)) (.branch 33 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_963
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.leaf (7))))),
  (.branch 19 (.branch 8 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.leaf (7))))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 27 (.leaf (3)) (.leaf (4))))),
  (.branch 23 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 8 (.leaf (-1)) (.leaf (-2)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-6))) (.branch 27 (.leaf (-8)) (.leaf (-9)))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 17 (.leaf (-16)) (.leaf (-17)))),
  (.branch 15 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.leaf (-2)),
  (.branch 30 (.branch 28 (.leaf (-9)) (.branch 29 (.leaf (-8)) (.leaf (-7)))) (.branch 32 (.branch 31 (.leaf (-6)) (.leaf (-5))) (.branch 33 (.leaf (-4)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 31 (.branch 18 (.leaf (-17)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 33 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_055_964 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.leaf (4))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (2))) (.branch 11 (.leaf (6)) (.leaf (3)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (2)) (.leaf (5))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (2)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (6))) (.branch 24 (.leaf (1)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (5)) (.leaf (3)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (4)) (.branch 33 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_964
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 26 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (2)) (.branch 29 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 9 (.leaf (-14)) (.leaf (-15)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 4 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.leaf (-11))),
  (.branch 15 (.branch 8 (.leaf (0)) (.leaf (-1))) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (-16))) (.branch 28 (.leaf (-17)) (.leaf (-18)))),
  (.branch 11 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 32 (.branch 27 (.leaf (-15)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 22 (.leaf (-5)) (.branch 28 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.branch 21 (.leaf (-11)) (.branch 30 (.leaf (-10)) (.leaf (-8)))) (.branch 32 (.leaf (-6)) (.branch 33 (.leaf (-4)) (.leaf (-2))))),
  (.branch 33 (.leaf (-4)) (.leaf (-3))),
  (.branch 31 (.branch 29 (.leaf (-18)) (.branch 30 (.leaf (-15)) (.leaf (-12)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 12 (.leaf (-1)) (.leaf (0)))]
def witnessD7_055_965 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (4)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (6))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_965
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.leaf (1))),
  (.branch 25 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.leaf (-26))),
  (.branch 25 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 32 (.branch 23 (.leaf (-14)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 21 (.branch 14 (.branch 11 (.branch 9 (.leaf (-26)) (.branch 10 (.leaf (-25)) (.leaf (-24)))) (.branch 12 (.leaf (-23)) (.branch 13 (.leaf (-22)) (.leaf (-21))))) (.branch 17 (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18)))) (.branch 19 (.branch 18 (.leaf (-17)) (.leaf (-16))) (.branch 20 (.leaf (-15)) (.leaf (-14)))))) (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_055_966 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (0))) (.branch 11 (.leaf (5)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (3)) (.leaf (5)))) (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (1)) (.leaf (6))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (3)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (2)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (3)) (.branch 33 (.leaf (5)) (.leaf (2))))))))
  code := certificateD7_966
  counts := ![(.branch 14 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 22 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 32 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 21 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 8 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-13)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.leaf (0)),
  (.branch 3 (.leaf (0)) (.leaf (-8))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 11 (.leaf (0)) (.branch 21 (.leaf (-1)) (.leaf (-4)))),
  (.branch 8 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 32 (.branch 23 (.leaf (-14)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 27 (.branch 21 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-3)))),
  (.branch 30 (.branch 17 (.branch 5 (.leaf (-15)) (.leaf (-14))) (.branch 29 (.leaf (-13)) (.leaf (-11)))) (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-7))) (.branch 33 (.leaf (-5)) (.leaf (-3))))),
  (.branch 22 (.leaf (-4)) (.leaf (-3))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-9)) (.leaf (-8))) (.branch 28 (.leaf (-7)) (.leaf (-6)))) (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_055_967 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (2)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (6)) (.leaf (4)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (1))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (5)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_967
  counts := ![(.branch 15 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 32 (.leaf (7)) (.leaf (8)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 25 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 31 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 26 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 33 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2)))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 18 (.leaf (-7)) (.leaf (-9)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-11)) (.leaf (-12)))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-19)) (.leaf (-20)))),
  (.leaf (0)),
  (.branch 12 (.leaf (0)) (.leaf (-5))),
  (.branch 4 (.leaf (0)) (.branch 20 (.leaf (-13)) (.leaf (-14))))]
  high := ![(.branch 28 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-6)))),
  (.branch 26 (.branch 14 (.leaf (-12)) (.branch 20 (.leaf (-11)) (.leaf (-10)))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 27 (.leaf (-4)) (.leaf (-3))),
  (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5)))),
  (.leaf (0)),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_055_968 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (0))) (.branch 11 (.leaf (3)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (0))) (.branch 15 (.leaf (1)) (.branch 16 (.leaf (5)) (.leaf (3))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (2))) (.branch 20 (.leaf (4)) (.leaf (6)))) (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (3)) (.leaf (5))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (0))) (.branch 28 (.leaf (4)) (.leaf (1)))) (.branch 31 (.branch 30 (.leaf (3)) (.leaf (0))) (.branch 32 (.leaf (2)) (.branch 33 (.leaf (5)) (.leaf (4))))))))
  code := certificateD7_968
  counts := ![(.branch 14 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 18 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 22 (.leaf (3)) (.branch 29 (.leaf (4)) (.leaf (5))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 32 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 24 (.leaf (3)) (.branch 30 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 4 (.leaf (0)) (.branch 21 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 2 (.leaf (0)) (.branch 15 (.leaf (-24)) (.leaf (-27)))),
  (.branch 5 (.leaf (0)) (.branch 32 (.leaf (-9)) (.leaf (-10)))),
  (.branch 3 (.leaf (0)) (.branch 30 (.leaf (-4)) (.leaf (-5)))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 4 (.leaf (0)) (.leaf (-13)))]
  high := ![(.branch 32 (.branch 19 (.leaf (-13)) (.leaf (-12))) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.branch 30 (.branch 16 (.leaf (-27)) (.branch 23 (.leaf (-26)) (.leaf (-25)))) (.branch 32 (.branch 31 (.leaf (-20)) (.leaf (-15))) (.branch 33 (.leaf (-10)) (.leaf (-5))))),
  (.branch 33 (.leaf (-10)) (.leaf (-5))),
  (.branch 32 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 33 (.leaf (-3)) (.leaf (-2)))),
  (.branch 21 (.leaf (-1)) (.leaf (0))),
  (.leaf (-2)),
  (.branch 27 (.branch 24 (.branch 22 (.leaf (-13)) (.branch 23 (.leaf (-12)) (.leaf (-11)))) (.branch 25 (.leaf (-10)) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_055_969 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (1)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (0)) (.leaf (3))) (.branch 11 (.leaf (0)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (0))) (.branch 15 (.leaf (4)) (.branch 16 (.leaf (0)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (5)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (3)) (.leaf (0))) (.branch 24 (.leaf (1)) (.leaf (4))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (0)) (.leaf (2))) (.branch 28 (.leaf (0)) (.leaf (6)))) (.branch 31 (.branch 30 (.leaf (1)) (.leaf (0))) (.branch 32 (.leaf (5)) (.branch 33 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_969
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (6))))) (.branch 26 (.branch 21 (.branch 18 (.leaf (7)) (.leaf (8))) (.branch 23 (.leaf (9)) (.leaf (10)))) (.branch 31 (.branch 28 (.leaf (11)) (.leaf (12))) (.branch 33 (.leaf (13)) (.leaf (14)))))),
  (.branch 13 (.branch 2 (.leaf (0)) (.branch 7 (.leaf (1)) (.leaf (2)))) (.branch 24 (.branch 19 (.leaf (3)) (.leaf (4))) (.branch 30 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 12 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-10))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-11)) (.leaf (-13)))),
  (.branch 5 (.leaf (0)) (.branch 27 (.leaf (-13)) (.leaf (-15)))),
  (.branch 10 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-17)) (.leaf (-19)))),
  (.branch 8 (.leaf (0)) (.leaf (-7))),
  (.branch 12 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 24 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 29 (.leaf (-8)) (.leaf (-7)))),
  (.branch 31 (.branch 25 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-9)) (.branch 33 (.leaf (-6)) (.leaf (-3))))),
  (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-13)) (.leaf (-11)))) (.branch 32 (.branch 31 (.leaf (-9)) (.leaf (-7))) (.branch 33 (.leaf (-5)) (.leaf (-3))))),
  (.branch 11 (.leaf (-3)) (.branch 23 (.leaf (-2)) (.leaf (0)))),
  (.branch 29 (.branch 27 (.branch 26 (.leaf (-19)) (.leaf (-17))) (.branch 28 (.leaf (-15)) (.leaf (-13)))) (.branch 31 (.branch 30 (.leaf (-11)) (.leaf (-9))) (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-5)) (.leaf (-3)))))),
  (.branch 21 (.branch 9 (.leaf (-7)) (.leaf (-6))) (.branch 33 (.leaf (-5)) (.leaf (-3)))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_055_970 : CycleWitness 7 where
  length := 34
  word := (.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (1))) (.branch 11 (.leaf (0)) (.leaf (5)))) (.branch 14 (.branch 13 (.leaf (2)) (.leaf (1))) (.branch 15 (.leaf (0)) (.branch 16 (.leaf (3)) (.leaf (2))))))) (.branch 25 (.branch 21 (.branch 19 (.branch 18 (.leaf (0)) (.leaf (1))) (.branch 20 (.leaf (4)) (.leaf (0)))) (.branch 23 (.branch 22 (.leaf (2)) (.leaf (1))) (.branch 24 (.leaf (0)) (.leaf (3))))) (.branch 29 (.branch 27 (.branch 26 (.leaf (2)) (.leaf (1))) (.branch 28 (.leaf (0)) (.leaf (6)))) (.branch 31 (.branch 30 (.leaf (2)) (.leaf (1))) (.branch 32 (.leaf (0)) (.branch 33 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_970
  counts := ![(.branch 15 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 11 (.leaf (3)) (.leaf (4))))) (.branch 24 (.branch 18 (.leaf (5)) (.branch 21 (.leaf (6)) (.leaf (7)))) (.branch 28 (.leaf (8)) (.branch 32 (.leaf (9)) (.leaf (10)))))),
  (.branch 14 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 23 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 27 (.leaf (6)) (.branch 31 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 7 (.leaf (-6)) (.branch 24 (.leaf (-7)) (.leaf (-8))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-9))) (.branch 10 (.leaf (-10)) (.branch 14 (.leaf (-11)) (.leaf (-12))))),
  (.leaf (0)),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-1)) (.leaf (-2)))),
  (.branch 3 (.leaf (0)) (.leaf (-14))),
  (.branch 12 (.leaf (0)) (.leaf (-22))),
  (.branch 29 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 29 (.branch 25 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-4)))),
  (.branch 32 (.leaf (-12)) (.branch 33 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.leaf (-2)),
  (.branch 27 (.branch 23 (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))) (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.leaf (-8))))) (.branch 30 (.branch 28 (.leaf (-7)) (.branch 29 (.leaf (-6)) (.leaf (-5)))) (.branch 32 (.branch 31 (.leaf (-4)) (.leaf (-3))) (.branch 33 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 23 (.branch 17 (.branch 14 (.branch 13 (.leaf (-22)) (.leaf (-21))) (.branch 15 (.leaf (-20)) (.branch 16 (.leaf (-19)) (.leaf (-18))))) (.branch 20 (.branch 18 (.leaf (-17)) (.branch 19 (.leaf (-16)) (.leaf (-15)))) (.branch 21 (.leaf (-14)) (.branch 22 (.leaf (-13)) (.leaf (-12)))))) (.branch 28 (.branch 25 (.branch 24 (.leaf (-11)) (.leaf (-10))) (.branch 26 (.leaf (-9)) (.branch 27 (.leaf (-8)) (.leaf (-7))))) (.branch 31 (.branch 29 (.leaf (-6)) (.branch 30 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 31 (.branch 30 (.leaf (-5)) (.leaf (-4))) (.branch 32 (.leaf (-3)) (.branch 33 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_055 : Fin 29 → CycleWitness 7 := ![witnessD7_055_942, witnessD7_055_943, witnessD7_055_944, witnessD7_055_945, witnessD7_055_946, witnessD7_055_947, witnessD7_055_948, witnessD7_055_949, witnessD7_055_950, witnessD7_055_951, witnessD7_055_952, witnessD7_055_953, witnessD7_055_954, witnessD7_055_955, witnessD7_055_956, witnessD7_055_957, witnessD7_055_958, witnessD7_055_959, witnessD7_055_960, witnessD7_055_961, witnessD7_055_962, witnessD7_055_963, witnessD7_055_964, witnessD7_055_965, witnessD7_055_966, witnessD7_055_967, witnessD7_055_968, witnessD7_055_969, witnessD7_055_970]
end RealPinwheel.FiveSixths


