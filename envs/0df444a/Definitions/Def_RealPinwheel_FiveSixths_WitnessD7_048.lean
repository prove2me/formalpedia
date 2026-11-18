-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_048
-- name    : RealPinwheel_FiveSixths_WitnessD7_048
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:54:46.18129+00:00
-- url     : https://prove2.me/theorems/107d8575-648a-4edc-83a0-d1a6d59babce
-- title:
--   Exact witness block D7_048
-- statement:
--   These exact witnesses represent words 751 through 776 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 751–776; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_048_750 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (5)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (2))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (5))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (2))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_750
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 10 (.leaf (0)) (.branch 29 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 20 (.leaf (-10)) (.branch 23 (.leaf (-11)) (.leaf (-12))))),
  (.branch 2 (.leaf (0)) (.leaf (-11))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 24 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-8)))),
  (.branch 27 (.branch 22 (.leaf (-11)) (.leaf (-10))) (.branch 32 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 36 (.branch 29 (.leaf (-11)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 25 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 34 (.branch 20 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048_751 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (2)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_751
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 14 (.leaf (0)) (.leaf (1))),
  (.branch 33 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 10 (.leaf (-15)) (.branch 13 (.leaf (-16)) (.leaf (-17))))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 14 (.leaf (0)) (.leaf (-24))),
  (.branch 33 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 33 (.leaf (-17)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 31 (.branch 26 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 32 (.leaf (-4)) (.leaf (-3))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 35 (.branch 25 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 26 (.branch 20 (.branch 17 (.branch 15 (.leaf (-24)) (.branch 16 (.leaf (-23)) (.leaf (-22)))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))) (.branch 23 (.branch 21 (.leaf (-18)) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))))) (.branch 32 (.branch 29 (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))) (.branch 30 (.leaf (-9)) (.branch 31 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_048_752 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (3))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_752
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.leaf (0)) (.leaf (1))),
  (.branch 38 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-9)) (.leaf (-10)))) (.branch 29 (.branch 13 (.leaf (-12)) (.leaf (-13))) (.branch 32 (.leaf (-14)) (.leaf (-15))))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 14 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.leaf (-19))),
  (.leaf (0))]
  high := ![(.branch 33 (.leaf (-15)) (.branch 37 (.leaf (-12)) (.leaf (-8)))),
  (.branch 36 (.branch 31 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-3)),
  (.branch 35 (.branch 34 (.leaf (-10)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))) (.branch 25 (.branch 24 (.leaf (-15)) (.leaf (-14))) (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_048_753 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (1))) (.branch 12 (.leaf (3)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (4)) (.leaf (2))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (3)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (6)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (2)) (.branch 37 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_753
  counts := ![(.branch 17 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 26 (.branch 21 (.leaf (5)) (.leaf (6))) (.branch 30 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 23 (.leaf (5)) (.leaf (6))) (.branch 32 (.leaf (7)) (.branch 37 (.leaf (8)) (.leaf (9)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 36 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 12 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 18 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 29 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 8 (.leaf (-14)) (.leaf (-15)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 23 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-17))),
  (.branch 22 (.leaf (0)) (.branch 27 (.leaf (-2)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 10 (.leaf (0)) (.leaf (-28))),
  (.branch 29 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 31 (.branch 22 (.leaf (-15)) (.leaf (-14))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-9)) (.leaf (-6))))),
  (.branch 24 (.leaf (-9)) (.branch 33 (.leaf (-8)) (.leaf (-6)))),
  (.branch 15 (.branch 4 (.leaf (-17)) (.leaf (-16))) (.branch 26 (.leaf (-15)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 28 (.leaf (-4)) (.branch 34 (.leaf (-3)) (.leaf (0)))),
  (.branch 35 (.branch 25 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 24 (.branch 17 (.branch 13 (.branch 11 (.leaf (-28)) (.branch 12 (.leaf (-27)) (.leaf (-26)))) (.branch 15 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 16 (.leaf (-23)) (.leaf (-22))))) (.branch 20 (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))))) (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048_754 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (3))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (4)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (5)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (2))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (4)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_754
  counts := ![(.branch 16 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 32 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 35 (.leaf (11)) (.leaf (12)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (-13)) (.leaf (-14)))) (.branch 13 (.branch 10 (.leaf (-15)) (.leaf (-16))) (.branch 16 (.leaf (-17)) (.leaf (-18))))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 3 (.leaf (0)) (.branch 25 (.leaf (-19)) (.leaf (-24)))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-23))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-4))))]
  high := ![(.branch 36 (.leaf (-18)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 35 (.branch 26 (.leaf (-24)) (.branch 34 (.leaf (-23)) (.leaf (-19)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-11)) (.leaf (-7))))),
  (.branch 15 (.branch 7 (.leaf (-7)) (.leaf (-6))) (.branch 23 (.leaf (-5)) (.branch 31 (.leaf (-4)) (.leaf (0))))),
  (.branch 37 (.leaf (-4)) (.leaf (-2))),
  (.branch 33 (.branch 19 (.branch 6 (.leaf (-23)) (.leaf (-22))) (.branch 32 (.leaf (-21)) (.leaf (-18)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 25 (.leaf (-4)) (.leaf (-3)))]
def witnessD7_048_755 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (6)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (5)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (2)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (2)) (.leaf (6)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (3))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (4)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_755
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 9 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 6 (.leaf (0)) (.leaf (-20))),
  (.branch 25 (.leaf (0)) (.leaf (-1))),
  (.branch 9 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 35 (.branch 25 (.leaf (-18)) (.branch 30 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 24 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 20 (.branch 7 (.leaf (-20)) (.leaf (-19))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048_756 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (5)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (3))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (1)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (2))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (1)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (4))) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (5)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (1)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (2))) (.branch 36 (.leaf (5)) (.branch 37 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_756
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 35 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 30 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.leaf (0)) (.branch 31 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 26 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-10)) (.leaf (-11)))),
  (.branch 11 (.branch 4 (.leaf (0)) (.leaf (-4))) (.branch 25 (.leaf (-5)) (.leaf (-7)))),
  (.branch 6 (.leaf (0)) (.branch 21 (.leaf (-2)) (.leaf (-3)))),
  (.branch 8 (.leaf (0)) (.branch 17 (.leaf (-3)) (.leaf (-4)))),
  (.branch 12 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 35 (.branch 25 (.leaf (-18)) (.branch 30 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 27 (.leaf (-4)) (.leaf (-3))),
  (.branch 36 (.branch 29 (.leaf (-11)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 35 (.branch 34 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 31 (.branch 22 (.leaf (-3)) (.leaf (-2))) (.branch 32 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.leaf (-4)) (.leaf (-2))),
  (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_048_757 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (1))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (5)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (6))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_757
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 8 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 27 (.leaf (-10)) (.leaf (-11)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.leaf (0)),
  (.branch 6 (.leaf (0)) (.branch 18 (.leaf (-20)) (.leaf (-22)))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 29 (.branch 21 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 36 (.branch 31 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.branch 35 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-4))))),
  (.branch 35 (.branch 24 (.leaf (-11)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 34 (.branch 32 (.branch 19 (.leaf (-22)) (.leaf (-21))) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (-3))]
def witnessD7_048_758 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (3))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (3))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (5))))))))
  code := certificateD7_758
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 19 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 38 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-9)) (.leaf (-11)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-6)))),
  (.branch 12 (.branch 4 (.leaf (0)) (.leaf (-7))) (.branch 19 (.leaf (-10)) (.leaf (-14)))),
  (.leaf (0)),
  (.branch 23 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 21 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-7)))),
  (.branch 33 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 34 (.branch 32 (.branch 20 (.leaf (-14)) (.leaf (-13))) (.branch 33 (.leaf (-12)) (.leaf (-11)))) (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.leaf (-7))))),
  (.leaf (0)),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048_759 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (0))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (4))) (.branch 17 (.leaf (1)) (.branch 18 (.leaf (0)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (0)) (.leaf (4)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (1)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (5))) (.branch 36 (.leaf (1)) (.branch 37 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_759
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 37 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 12 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 31 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 20 (.leaf (-11)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 13 (.leaf (-9)) (.leaf (-11)))),
  (.branch 3 (.leaf (0)) (.branch 12 (.leaf (-13)) (.leaf (-14)))),
  (.branch 7 (.leaf (0)) (.branch 26 (.leaf (-4)) (.leaf (-7)))),
  (.branch 16 (.branch 4 (.leaf (0)) (.leaf (-9))) (.branch 28 (.leaf (-10)) (.leaf (-11)))),
  (.branch 9 (.leaf (0)) (.leaf (-4))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 21 (.leaf (-12)) (.branch 34 (.leaf (-11)) (.leaf (-7)))),
  (.branch 33 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5)))),
  (.branch 34 (.branch 32 (.leaf (-14)) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 30 (.branch 28 (.branch 27 (.leaf (-7)) (.leaf (-6))) (.branch 29 (.leaf (-5)) (.leaf (-4)))) (.branch 32 (.branch 31 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-11)) (.leaf (-10))) (.branch 31 (.leaf (-9)) (.branch 32 (.leaf (-8)) (.leaf (-7))))) (.branch 35 (.branch 34 (.leaf (-6)) (.leaf (-5))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_048_760 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (2)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (4))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (3)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (2)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (3))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (2)) (.leaf (6)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (4))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (3)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_760
  counts := ![(.branch 15 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.leaf (3)))) (.branch 24 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 29 (.leaf (6)) (.branch 34 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 28 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 5 (.leaf (-15)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.branch 16 (.leaf (-11)) (.leaf (-12)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-7))),
  (.branch 9 (.leaf (0)) (.leaf (-29))),
  (.branch 28 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 35 (.branch 25 (.leaf (-18)) (.branch 30 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 26 (.leaf (-1)) (.leaf (0))),
  (.branch 24 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 23 (.branch 16 (.branch 12 (.branch 10 (.leaf (-29)) (.branch 11 (.leaf (-28)) (.leaf (-27)))) (.branch 14 (.branch 13 (.leaf (-26)) (.leaf (-25))) (.branch 15 (.leaf (-24)) (.leaf (-23))))) (.branch 19 (.branch 17 (.leaf (-22)) (.branch 18 (.leaf (-21)) (.leaf (-20)))) (.branch 21 (.branch 20 (.leaf (-19)) (.leaf (-18))) (.branch 22 (.leaf (-17)) (.leaf (-16)))))) (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-10)) (.leaf (-9))) (.branch 31 (.leaf (-8)) (.branch 32 (.leaf (-7)) (.leaf (-6))))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048_761 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (1)) (.leaf (0))) (.branch 22 (.leaf (3)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (6)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_761
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 21 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 26 (.leaf (3)) (.branch 34 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 23 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 11 (.branch 2 (.leaf (0)) (.leaf (-17))) (.branch 15 (.leaf (-21)) (.leaf (-26)))),
  (.branch 3 (.leaf (0)) (.branch 10 (.leaf (-14)) (.leaf (-16)))),
  (.branch 22 (.leaf (0)) (.branch 29 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 29 (.branch 2 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 16 (.leaf (-26)) (.branch 21 (.leaf (-25)) (.leaf (-24)))) (.branch 36 (.branch 31 (.leaf (-23)) (.leaf (-22))) (.branch 37 (.leaf (-16)) (.leaf (-10))))),
  (.branch 27 (.branch 11 (.leaf (-16)) (.branch 19 (.leaf (-15)) (.leaf (-14)))) (.branch 36 (.branch 35 (.leaf (-13)) (.leaf (-10))) (.branch 37 (.leaf (-7)) (.leaf (-4))))),
  (.leaf (-3)),
  (.branch 35 (.branch 24 (.leaf (-11)) (.branch 34 (.leaf (-10)) (.leaf (-8)))) (.branch 36 (.leaf (-6)) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.branch 28 (.leaf (-1)) (.leaf (0))))]
def witnessD7_048_762 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (0))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (0)) (.leaf (2))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (4)) (.branch 18 (.leaf (0)) (.leaf (6))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (2)) (.leaf (1))) (.branch 22 (.leaf (0)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (5))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (4)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (6))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (5)) (.leaf (3))))))))
  code := certificateD7_762
  counts := ![(.branch 18 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 22 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 27 (.branch 20 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 23 (.branch 8 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 38 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 24 (.leaf (-3)) (.leaf (-4)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 9 (.branch 3 (.leaf (0)) (.leaf (-11))) (.branch 14 (.leaf (-13)) (.branch 20 (.leaf (-18)) (.leaf (-20))))),
  (.branch 15 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.branch 29 (.leaf (-26)) (.leaf (-27)))),
  (.branch 12 (.leaf (0)) (.branch 37 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.leaf (-17)))]
  high := ![(.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 36 (.branch 31 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.branch 35 (.branch 21 (.leaf (-20)) (.branch 28 (.leaf (-19)) (.leaf (-18)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-12)) (.leaf (-9))))),
  (.branch 16 (.leaf (-1)) (.leaf (0))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-27)) (.leaf (-24))) (.branch 32 (.leaf (-21)) (.leaf (-18)))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.leaf (-3)),
  (.branch 34 (.branch 6 (.leaf (-17)) (.branch 20 (.leaf (-16)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-13)) (.leaf (-11))) (.branch 37 (.leaf (-9)) (.leaf (-7)))))]
def witnessD7_048_763 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (0)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (4)) (.branch 13 (.leaf (2)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (6)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.leaf (5)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (6)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_763
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 22 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 37 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2)))),
  (.branch 15 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 10 (.branch 1 (.leaf (0)) (.leaf (-9))) (.branch 29 (.leaf (-12)) (.leaf (-14)))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.branch 22 (.leaf (-2)) (.leaf (-3)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (-6))) (.branch 31 (.leaf (-7)) (.leaf (-8)))),
  (.branch 12 (.leaf (0)) (.leaf (-1))),
  (.branch 4 (.leaf (0)) (.leaf (-15))),
  (.branch 15 (.leaf (0)) (.leaf (-4)))]
  high := ![(.branch 30 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-8)))),
  (.branch 31 (.branch 26 (.leaf (-14)) (.leaf (-13))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.leaf (-3)),
  (.branch 34 (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2))))),
  (.branch 13 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_048_764 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (4))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (6))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (4))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_764
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 32 (.leaf (9)) (.branch 36 (.leaf (10)) (.leaf (11)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 21 (.leaf (-10)) (.branch 24 (.leaf (-14)) (.leaf (-16))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-24))) (.branch 23 (.leaf (-27)) (.leaf (-29)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-7))),
  (.branch 10 (.leaf (0)) (.leaf (-28))),
  (.branch 30 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 29 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-14)) (.branch 37 (.leaf (-13)) (.leaf (-10))))),
  (.branch 35 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.leaf (-5)) (.branch 32 (.leaf (-4)) (.leaf (-3)))),
  (.branch 36 (.branch 26 (.leaf (-7)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2)))),
  (.branch 24 (.branch 17 (.branch 13 (.branch 11 (.leaf (-28)) (.branch 12 (.leaf (-27)) (.leaf (-26)))) (.branch 15 (.branch 14 (.leaf (-25)) (.leaf (-24))) (.branch 16 (.leaf (-23)) (.leaf (-22))))) (.branch 20 (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19)))) (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))))) (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_048_765 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (4))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (2))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (0)) (.leaf (5))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (1)) (.leaf (0))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (3)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (4))) (.branch 26 (.leaf (3)) (.branch 27 (.leaf (2)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (6))) (.branch 31 (.leaf (3)) (.branch 32 (.leaf (0)) (.leaf (2))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (5))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_765
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 28 (.branch 21 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 32 (.leaf (9)) (.branch 36 (.leaf (10)) (.leaf (11)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 6 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 16 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-8))) (.branch 21 (.leaf (-10)) (.branch 24 (.leaf (-14)) (.leaf (-16))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-24))) (.branch 23 (.leaf (-27)) (.leaf (-29)))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 3 (.leaf (0)) (.leaf (-5))),
  (.branch 6 (.leaf (0)) (.leaf (-13))),
  (.branch 16 (.leaf (0)) (.leaf (-3))),
  (.branch 10 (.leaf (0)) (.leaf (-9)))]
  high := ![(.branch 29 (.branch 25 (.leaf (-16)) (.leaf (-15))) (.branch 33 (.leaf (-14)) (.branch 37 (.leaf (-13)) (.leaf (-10))))),
  (.branch 35 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 15 (.leaf (-5)) (.branch 32 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.branch 28 (.branch 26 (.leaf (-13)) (.branch 27 (.leaf (-12)) (.leaf (-11)))) (.branch 29 (.leaf (-10)) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))),
  (.branch 33 (.branch 31 (.branch 11 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048_766 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (4))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (1)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (5))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (1)) (.leaf (0))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (3)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (4)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (3))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (5)) (.branch 37 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_766
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 15 (.branch 2 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 28 (.branch 21 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 22 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 29 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 17 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 5 (.leaf (0)) (.branch 24 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-23))) (.branch 25 (.leaf (-26)) (.leaf (-27)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 17 (.branch 11 (.leaf (0)) (.leaf (-1))) (.branch 36 (.leaf (-7)) (.leaf (-12)))),
  (.branch 5 (.leaf (0)) (.leaf (-14)))]
  high := ![(.branch 32 (.branch 24 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 35 (.branch 22 (.leaf (-13)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.leaf (0)),
  (.branch 35 (.branch 26 (.leaf (-27)) (.branch 34 (.leaf (-25)) (.leaf (-20)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 7 (.leaf (-8)) (.branch 30 (.leaf (-7)) (.leaf (-5)))),
  (.branch 37 (.leaf (-12)) (.leaf (-11))),
  (.branch 31 (.branch 27 (.branch 25 (.leaf (-14)) (.branch 26 (.leaf (-13)) (.leaf (-12)))) (.branch 29 (.branch 28 (.leaf (-11)) (.leaf (-10))) (.branch 30 (.leaf (-9)) (.leaf (-8))))) (.branch 34 (.branch 32 (.leaf (-7)) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048_767 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (5))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (0))) (.branch 12 (.leaf (6)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (3))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (1)) (.leaf (5))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (4)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (6))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (2)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (4))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (6))))))))
  code := certificateD7_767
  counts := ![(.branch 17 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 27 (.branch 20 (.leaf (6)) (.branch 24 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 30 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 10 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 16 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-24))) (.branch 23 (.leaf (-27)) (.leaf (-29)))),
  (.branch 4 (.leaf (0)) (.leaf (-10))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-29)) (.leaf (-30)))),
  (.branch 9 (.leaf (0)) (.leaf (-11))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-20)) (.leaf (-21)))),
  (.branch 12 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 21 (.leaf (-13)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 35 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 16 (.branch 5 (.leaf (-10)) (.leaf (-9))) (.branch 27 (.leaf (-8)) (.leaf (-7)))),
  (.branch 33 (.branch 30 (.branch 29 (.leaf (-30)) (.leaf (-27))) (.branch 31 (.leaf (-24)) (.branch 32 (.leaf (-21)) (.leaf (-18))))) (.branch 35 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 23 (.branch 10 (.leaf (-11)) (.leaf (-10))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 34 (.branch 32 (.leaf (-21)) (.branch 33 (.leaf (-18)) (.leaf (-15)))) (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 13 (.leaf (-2)) (.branch 26 (.leaf (-1)) (.leaf (0))))]
def witnessD7_048_768 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (2)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (6))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (5)) (.branch 13 (.leaf (1)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (4))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (0))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (6)) (.leaf (2))) (.branch 22 (.leaf (0)) (.leaf (1)))) (.branch 25 (.branch 24 (.leaf (5)) (.leaf (3))) (.branch 26 (.leaf (4)) (.branch 27 (.leaf (0)) (.leaf (2)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (6)) (.branch 32 (.leaf (2)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (4)) (.branch 37 (.leaf (5)) (.leaf (2))))))))
  code := certificateD7_768
  counts := ![(.branch 19 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 22 (.leaf (5)) (.leaf (6))) (.branch 30 (.leaf (7)) (.branch 35 (.leaf (8)) (.leaf (9)))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 11 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 16 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 24 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 5 (.branch 1 (.leaf (0)) (.leaf (-10))) (.branch 22 (.leaf (-11)) (.branch 30 (.leaf (-12)) (.leaf (-14))))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-24))) (.branch 23 (.leaf (-27)) (.leaf (-29)))),
  (.branch 15 (.branch 4 (.leaf (0)) (.leaf (-2))) (.branch 32 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-19)) (.leaf (-26)))),
  (.branch 8 (.leaf (0)) (.branch 16 (.leaf (-5)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.branch 24 (.leaf (-2)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.branch 31 (.leaf (-7)) (.leaf (-8))))]
  high := ![(.branch 36 (.branch 31 (.leaf (-14)) (.leaf (-12))) (.branch 37 (.leaf (-9)) (.leaf (-6)))),
  (.branch 35 (.branch 24 (.leaf (-29)) (.leaf (-28))) (.branch 36 (.leaf (-21)) (.branch 37 (.leaf (-14)) (.leaf (-7))))),
  (.branch 34 (.branch 33 (.leaf (-4)) (.leaf (-3))) (.branch 35 (.leaf (-2)) (.branch 36 (.leaf (-1)) (.leaf (0))))),
  (.branch 34 (.branch 18 (.branch 10 (.leaf (-26)) (.leaf (-25))) (.branch 26 (.leaf (-24)) (.leaf (-23)))) (.branch 36 (.branch 35 (.leaf (-19)) (.leaf (-15))) (.branch 37 (.leaf (-11)) (.leaf (-7))))),
  (.branch 27 (.branch 17 (.leaf (-10)) (.leaf (-9))) (.branch 37 (.leaf (-8)) (.leaf (-5)))),
  (.branch 25 (.leaf (-4)) (.leaf (-3))),
  (.branch 34 (.branch 32 (.leaf (-8)) (.branch 33 (.leaf (-7)) (.leaf (-6)))) (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_048_769 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (4))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (4)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_769
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 4 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 34 (.leaf (-9)) (.leaf (-10)))),
  (.branch 19 (.leaf (0)) (.leaf (-2))),
  (.branch 4 (.leaf (0)) (.leaf (-34))),
  (.branch 23 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 29 (.branch 21 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 36 (.branch 31 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 34 (.leaf (-2)) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 21 (.branch 12 (.branch 8 (.branch 6 (.branch 5 (.leaf (-34)) (.leaf (-33))) (.branch 7 (.leaf (-32)) (.leaf (-31)))) (.branch 10 (.branch 9 (.leaf (-30)) (.leaf (-29))) (.branch 11 (.leaf (-28)) (.leaf (-27))))) (.branch 16 (.branch 14 (.branch 13 (.leaf (-26)) (.leaf (-25))) (.branch 15 (.leaf (-24)) (.leaf (-23)))) (.branch 18 (.branch 17 (.leaf (-22)) (.leaf (-21))) (.branch 19 (.leaf (-20)) (.branch 20 (.leaf (-19)) (.leaf (-18))))))) (.branch 29 (.branch 25 (.branch 23 (.branch 22 (.leaf (-17)) (.leaf (-16))) (.branch 24 (.leaf (-15)) (.leaf (-14)))) (.branch 27 (.branch 26 (.leaf (-13)) (.leaf (-12))) (.branch 28 (.leaf (-11)) (.leaf (-10))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048_770 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (0)) (.leaf (2))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (4)) (.leaf (0)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (0)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (3)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (4))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (3)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (0)) (.leaf (2))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (5)) (.leaf (0)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (0)) (.leaf (4))))) (.branch 35 (.branch 34 (.leaf (3)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_770
  counts := ![(.branch 17 (.branch 5 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 9 (.leaf (2)) (.branch 13 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 20 (.leaf (5)) (.branch 24 (.leaf (6)) (.leaf (7)))) (.branch 32 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 6 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 22 (.leaf (3)) (.leaf (4))) (.branch 34 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 23 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-14))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 12 (.branch 6 (.leaf (0)) (.leaf (-1))) (.branch 18 (.leaf (-2)) (.leaf (-3)))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-7))) (.branch 34 (.leaf (-9)) (.leaf (-10)))),
  (.branch 8 (.leaf (0)) (.branch 19 (.leaf (-5)) (.leaf (-7)))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-15)))]
  high := ![(.branch 29 (.branch 21 (.leaf (-14)) (.branch 25 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.leaf (-11)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 36 (.branch 31 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (-3)),
  (.branch 36 (.branch 35 (.leaf (-10)) (.leaf (-8))) (.branch 37 (.leaf (-6)) (.leaf (-4)))),
  (.branch 35 (.branch 20 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 30 (.branch 26 (.branch 24 (.leaf (-15)) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048_771 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (3)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (2)) (.branch 13 (.leaf (1)) (.leaf (6))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (2)) (.branch 18 (.leaf (3)) (.leaf (1))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (5)) (.leaf (0))) (.branch 22 (.leaf (2)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (3))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (2)) (.leaf (6)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (0))) (.branch 31 (.leaf (4)) (.branch 32 (.leaf (5)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (2)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (4)) (.leaf (2))))))))
  code := certificateD7_771
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 36 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.leaf (7))))),
  (.branch 22 (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 34 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 38 (.leaf (6)) (.leaf (7))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 25 (.leaf (3)) (.branch 33 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 31 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 20 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 32 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 30 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 29 (.leaf (-24)) (.leaf (-25)))),
  (.branch 22 (.branch 5 (.leaf (0)) (.leaf (-1))) (.branch 27 (.leaf (-2)) (.leaf (-3)))),
  (.branch 10 (.branch 3 (.leaf (0)) (.leaf (-23))) (.branch 25 (.leaf (-26)) (.leaf (-27)))),
  (.branch 23 (.branch 15 (.leaf (0)) (.leaf (-3))) (.branch 31 (.leaf (-4)) (.branch 37 (.leaf (-5)) (.leaf (-8))))),
  (.branch 7 (.leaf (0)) (.branch 32 (.leaf (-17)) (.leaf (-18)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-19)) (.leaf (-26))))]
  high := ![(.branch 31 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 36 (.branch 30 (.leaf (-25)) (.leaf (-21))) (.branch 37 (.leaf (-14)) (.leaf (-7)))),
  (.branch 35 (.branch 28 (.leaf (-3)) (.leaf (-2))) (.branch 36 (.leaf (-1)) (.leaf (0)))),
  (.branch 35 (.branch 26 (.leaf (-27)) (.branch 34 (.leaf (-25)) (.leaf (-20)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.leaf (-8)),
  (.branch 35 (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-15)) (.leaf (-12)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3))))),
  (.branch 32 (.branch 29 (.branch 15 (.leaf (-26)) (.leaf (-25))) (.branch 30 (.leaf (-23)) (.branch 31 (.leaf (-21)) (.leaf (-19))))) (.branch 35 (.branch 33 (.leaf (-17)) (.branch 34 (.leaf (-15)) (.leaf (-13)))) (.branch 36 (.leaf (-11)) (.branch 37 (.leaf (-9)) (.leaf (-7))))))]
def witnessD7_048_772 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (1))) (.branch 7 (.leaf (0)) (.branch 8 (.leaf (5)) (.leaf (3)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (0)) (.leaf (2))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (6)) (.leaf (0))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (2)) (.leaf (3))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (1))) (.branch 26 (.leaf (0)) (.branch 27 (.leaf (4)) (.leaf (3)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (0)) (.leaf (2))) (.branch 31 (.leaf (1)) (.branch 32 (.leaf (6)) (.leaf (0))))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (2)) (.leaf (3))))))))
  code := certificateD7_772
  counts := ![(.branch 17 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5))))) (.branch 26 (.branch 20 (.leaf (6)) (.branch 23 (.leaf (7)) (.leaf (8)))) (.branch 33 (.branch 29 (.leaf (9)) (.leaf (10))) (.branch 36 (.leaf (11)) (.leaf (12)))))),
  (.branch 16 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 31 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 13 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-13))) (.branch 7 (.leaf (-14)) (.branch 10 (.leaf (-15)) (.leaf (-16))))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-3))) (.branch 25 (.leaf (-4)) (.leaf (-5)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-4)) (.leaf (-5)))),
  (.branch 9 (.leaf (0)) (.leaf (-1))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (-10))) (.branch 27 (.leaf (-11)) (.leaf (-12)))),
  (.branch 8 (.leaf (0)) (.leaf (-5))),
  (.branch 13 (.leaf (0)) (.leaf (-6)))]
  high := ![(.branch 30 (.leaf (-16)) (.branch 37 (.leaf (-12)) (.leaf (-6)))),
  (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 31 (.leaf (-5)) (.leaf (-3))),
  (.branch 29 (.leaf (-1)) (.leaf (0))),
  (.branch 32 (.branch 29 (.branch 28 (.leaf (-12)) (.leaf (-11))) (.branch 30 (.leaf (-10)) (.branch 31 (.leaf (-9)) (.leaf (-8))))) (.branch 35 (.branch 33 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))),
  (.branch 36 (.branch 35 (.leaf (-5)) (.leaf (-4))) (.branch 37 (.leaf (-3)) (.leaf (-2)))),
  (.branch 35 (.branch 33 (.leaf (-6)) (.branch 34 (.leaf (-5)) (.leaf (-4)))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_048_773 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (0)) (.leaf (5)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (1))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (3))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (1))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (6)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (5)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (2)) (.leaf (3))) (.branch 26 (.leaf (1)) (.branch 27 (.leaf (0)) (.leaf (4)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (2)) (.leaf (1))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (3))))) (.branch 35 (.branch 34 (.leaf (5)) (.leaf (1))) (.branch 36 (.leaf (0)) (.branch 37 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_773
  counts := ![(.branch 17 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 36 (.leaf (9)) (.leaf (10)))))),
  (.branch 16 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 26 (.branch 21 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 10 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 32 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 15 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.leaf (3)))),
  (.branch 22 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 18 (.leaf (0)) (.branch 37 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 4 (.branch 1 (.leaf (0)) (.leaf (-3))) (.branch 23 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-11)) (.leaf (-13)))),
  (.branch 13 (.leaf (0)) (.branch 32 (.leaf (-2)) (.leaf (-3)))),
  (.branch 14 (.branch 6 (.leaf (0)) (.leaf (-4))) (.branch 33 (.leaf (-6)) (.leaf (-7)))),
  (.branch 3 (.leaf (0)) (.branch 15 (.leaf (-29)) (.leaf (-31)))),
  (.branch 9 (.leaf (0)) (.branch 34 (.leaf (-11)) (.leaf (-12)))),
  (.branch 18 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 32 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3)))),
  (.branch 36 (.branch 31 (.leaf (-13)) (.leaf (-12))) (.branch 37 (.leaf (-8)) (.leaf (-4)))),
  (.branch 34 (.branch 33 (.leaf (-3)) (.leaf (-2))) (.branch 35 (.leaf (-1)) (.leaf (0)))),
  (.branch 35 (.branch 34 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.branch 37 (.leaf (-4)) (.leaf (-3))))),
  (.branch 32 (.branch 29 (.branch 16 (.leaf (-31)) (.leaf (-30))) (.branch 30 (.leaf (-27)) (.branch 31 (.leaf (-24)) (.leaf (-21))))) (.branch 35 (.branch 33 (.leaf (-18)) (.branch 34 (.leaf (-15)) (.leaf (-12)))) (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-6)) (.leaf (-3)))))),
  (.branch 36 (.branch 35 (.leaf (-12)) (.leaf (-9))) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.leaf (-1))]
def witnessD7_048_774 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (4)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (0))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (3)) (.leaf (0))) (.branch 12 (.leaf (1)) (.branch 13 (.leaf (4)) (.leaf (5))))) (.branch 16 (.branch 15 (.leaf (2)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (6))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (2))) (.branch 22 (.leaf (4)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (1)) (.leaf (0))) (.branch 26 (.leaf (5)) (.branch 27 (.leaf (2)) (.leaf (1)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (3)) (.leaf (0))) (.branch 31 (.leaf (2)) (.branch 32 (.leaf (4)) (.leaf (6))))) (.branch 35 (.branch 34 (.leaf (1)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_774
  counts := ![(.branch 16 (.branch 6 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.leaf (3)))) (.branch 25 (.branch 20 (.leaf (4)) (.leaf (5))) (.branch 30 (.leaf (6)) (.branch 35 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 9 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 15 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 27 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 29 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (2)) (.branch 32 (.leaf (3)) (.leaf (4))))),
  (.branch 26 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 19 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-15))),
  (.branch 12 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 28 (.leaf (-15)) (.leaf (-18)))),
  (.branch 9 (.branch 5 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-7)) (.leaf (-9)))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-7)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 7 (.leaf (0)) (.branch 19 (.leaf (-6)) (.leaf (-7))))]
  high := ![(.branch 31 (.branch 21 (.leaf (-15)) (.branch 26 (.leaf (-14)) (.leaf (-13)))) (.branch 36 (.leaf (-12)) (.branch 37 (.leaf (-8)) (.leaf (-4))))),
  (.branch 35 (.branch 29 (.leaf (-18)) (.leaf (-17))) (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-11)) (.leaf (-8))))),
  (.branch 32 (.leaf (-9)) (.leaf (-8))),
  (.branch 30 (.leaf (-8)) (.branch 37 (.leaf (-6)) (.leaf (-3)))),
  (.branch 34 (.branch 23 (.leaf (-13)) (.branch 33 (.leaf (-12)) (.leaf (-10)))) (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-6))) (.branch 37 (.leaf (-4)) (.leaf (-2))))),
  (.leaf (0)),
  (.branch 35 (.branch 20 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.leaf (-4)) (.branch 37 (.leaf (-3)) (.leaf (-2)))))]
def witnessD7_048_775 : CycleWitness 7 where
  length := 38
  word := (.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (5)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (1))) (.branch 7 (.leaf (2)) (.branch 8 (.leaf (0)) (.leaf (4)))))) (.branch 14 (.branch 11 (.branch 10 (.leaf (1)) (.leaf (3))) (.branch 12 (.leaf (0)) (.branch 13 (.leaf (2)) (.leaf (1))))) (.branch 16 (.branch 15 (.leaf (4)) (.leaf (0))) (.branch 17 (.leaf (3)) (.branch 18 (.leaf (1)) (.leaf (2))))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf (0)) (.leaf (1))) (.branch 22 (.leaf (6)) (.leaf (0)))) (.branch 25 (.branch 24 (.leaf (3)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 27 (.leaf (0)) (.leaf (4)))))) (.branch 33 (.branch 30 (.branch 29 (.leaf (1)) (.leaf (3))) (.branch 31 (.leaf (0)) (.branch 32 (.leaf (2)) (.leaf (1))))) (.branch 35 (.branch 34 (.leaf (4)) (.leaf (0))) (.branch 36 (.leaf (3)) (.branch 37 (.leaf (1)) (.leaf (2))))))))
  code := certificateD7_775
  counts := ![(.branch 16 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.branch 12 (.leaf (3)) (.leaf (4))))) (.branch 27 (.branch 20 (.leaf (5)) (.branch 23 (.leaf (6)) (.leaf (7)))) (.branch 31 (.leaf (8)) (.branch 35 (.leaf (9)) (.leaf (10)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 29 (.branch 21 (.leaf (5)) (.branch 25 (.leaf (6)) (.leaf (7)))) (.branch 33 (.leaf (8)) (.branch 37 (.leaf (9)) (.leaf (10)))))),
  (.branch 19 (.branch 7 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 36 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 34 (.leaf (3)) (.leaf (4))))),
  (.branch 3 (.leaf (0)) (.leaf (1))),
  (.branch 22 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-14)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-9))),
  (.leaf (0)),
  (.branch 11 (.branch 5 (.leaf (0)) (.leaf (-4))) (.branch 17 (.leaf (-5)) (.leaf (-6)))),
  (.branch 15 (.branch 9 (.leaf (0)) (.leaf (-3))) (.branch 34 (.leaf (-9)) (.leaf (-14)))),
  (.branch 3 (.leaf (0)) (.leaf (-35))),
  (.branch 22 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 32 (.branch 24 (.leaf (-18)) (.branch 28 (.leaf (-17)) (.leaf (-16)))) (.branch 36 (.leaf (-15)) (.branch 37 (.leaf (-10)) (.leaf (-5))))),
  (.branch 26 (.branch 22 (.leaf (-9)) (.leaf (-8))) (.branch 30 (.leaf (-7)) (.branch 34 (.leaf (-6)) (.leaf (-5))))),
  (.leaf (0)),
  (.branch 37 (.leaf (-6)) (.leaf (-3))),
  (.branch 36 (.branch 35 (.leaf (-14)) (.leaf (-13))) (.branch 37 (.leaf (-12)) (.leaf (-11)))),
  (.branch 20 (.branch 11 (.branch 7 (.branch 5 (.branch 4 (.leaf (-35)) (.leaf (-34))) (.branch 6 (.leaf (-33)) (.leaf (-32)))) (.branch 9 (.branch 8 (.leaf (-31)) (.leaf (-30))) (.branch 10 (.leaf (-29)) (.leaf (-28))))) (.branch 15 (.branch 13 (.branch 12 (.leaf (-27)) (.leaf (-26))) (.branch 14 (.leaf (-25)) (.leaf (-24)))) (.branch 17 (.branch 16 (.leaf (-23)) (.leaf (-22))) (.branch 18 (.leaf (-21)) (.branch 19 (.leaf (-20)) (.leaf (-19))))))) (.branch 29 (.branch 24 (.branch 22 (.branch 21 (.leaf (-18)) (.leaf (-17))) (.branch 23 (.leaf (-16)) (.leaf (-15)))) (.branch 26 (.branch 25 (.leaf (-14)) (.leaf (-13))) (.branch 27 (.leaf (-12)) (.branch 28 (.leaf (-11)) (.leaf (-10)))))) (.branch 33 (.branch 31 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 32 (.leaf (-7)) (.leaf (-6)))) (.branch 35 (.branch 34 (.leaf (-5)) (.leaf (-4))) (.branch 36 (.leaf (-3)) (.branch 37 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 30 (.branch 26 (.branch 24 (.branch 23 (.leaf (-16)) (.leaf (-15))) (.branch 25 (.leaf (-14)) (.leaf (-13)))) (.branch 28 (.branch 27 (.leaf (-12)) (.leaf (-11))) (.branch 29 (.leaf (-10)) (.leaf (-9))))) (.branch 34 (.branch 32 (.branch 31 (.leaf (-8)) (.leaf (-7))) (.branch 33 (.leaf (-6)) (.leaf (-5)))) (.branch 36 (.branch 35 (.leaf (-4)) (.leaf (-3))) (.branch 37 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_048 : Fin 26 → CycleWitness 7 := ![witnessD7_048_750, witnessD7_048_751, witnessD7_048_752, witnessD7_048_753, witnessD7_048_754, witnessD7_048_755, witnessD7_048_756, witnessD7_048_757, witnessD7_048_758, witnessD7_048_759, witnessD7_048_760, witnessD7_048_761, witnessD7_048_762, witnessD7_048_763, witnessD7_048_764, witnessD7_048_765, witnessD7_048_766, witnessD7_048_767, witnessD7_048_768, witnessD7_048_769, witnessD7_048_770, witnessD7_048_771, witnessD7_048_772, witnessD7_048_773, witnessD7_048_774, witnessD7_048_775]
end RealPinwheel.FiveSixths


