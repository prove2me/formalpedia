-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_042
-- name    : RealPinwheel_FiveSixths_WitnessD7_042
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:49:12.690898+00:00
-- url     : https://prove2.me/theorems/4f947dad-9368-431f-b69a-3b308994e449
-- title:
--   Exact witness block D7_042
-- statement:
--   These exact witnesses represent words 604 through 626 of source certificate file D7. They store the task word, prefix counts, and prefix and suffix discrepancy minima as balanced step-function trees.
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   The tables carry no correctness assumption. A separate theorem checks their local recurrences and inequalities in the Lean kernel, and witness soundness transfers those checks to all-window validity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 604–626; https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Witness
import Definitions.Def_RealPinwheel_FiveSixths_CertificateD7
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessD7_042_603 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (0)) (.leaf (5))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_603
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 18 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 32 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 16 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.leaf (0)) (.leaf (1))),
  (.branch 42 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.leaf (-15)))),
  (.branch 5 (.leaf (0)) (.branch 11 (.leaf (-2)) (.leaf (-3)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 16 (.branch 9 (.leaf (0)) (.leaf (-4))) (.branch 37 (.leaf (-10)) (.leaf (-15)))),
  (.branch 21 (.leaf (0)) (.leaf (-21))),
  (.leaf (0))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 40 (.branch 34 (.leaf (-15)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 33 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11))))),
  (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.branch 25 (.leaf (-18)) (.leaf (-17))))) (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (0))]
def witnessD7_042_604 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (4))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (0)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (1)) (.branch 30 (.leaf (0)) (.leaf (3)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (4))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (2))))))))
  code := certificateD7_604
  counts := ![(.branch 19 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 14 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 30 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (11)))) (.branch 35 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 38 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 8 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 29 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 37 (.leaf (5)) (.leaf (6))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 33 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-13)) (.leaf (-18)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.leaf (0)),
  (.branch 16 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))) (.branch 31 (.leaf (-8)) (.branch 37 (.leaf (-9)) (.leaf (-11))))),
  (.branch 12 (.branch 5 (.leaf (0)) (.leaf (-8))) (.branch 33 (.leaf (-14)) (.leaf (-19)))),
  (.branch 20 (.leaf (0)) (.leaf (-22))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 33 (.branch 25 (.leaf (-18)) (.leaf (-17))) (.branch 41 (.leaf (-16)) (.leaf (-8)))),
  (.branch 40 (.branch 24 (.leaf (-13)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.leaf (0)),
  (.branch 39 (.branch 38 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-19)) (.leaf (-18))) (.branch 36 (.leaf (-17)) (.leaf (-16)))) (.branch 39 (.branch 38 (.leaf (-15)) (.leaf (-14))) (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-12)) (.leaf (-11)))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))) (.branch 28 (.branch 26 (.leaf (-17)) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_042_605 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (3)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (6))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (0)) (.leaf (5)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (2))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (3)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (4)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (0)) (.leaf (4))))))))
  code := certificateD7_605
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 2 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 23 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 32 (.leaf (3)) (.branch 40 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 18 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 39 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.leaf (-13))),
  (.branch 7 (.leaf (0)) (.branch 23 (.leaf (-3)) (.leaf (-5)))),
  (.branch 4 (.leaf (0)) (.branch 14 (.leaf (-13)) (.leaf (-14)))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (-2)) (.leaf (-3)))),
  (.branch 5 (.leaf (0)) (.branch 18 (.leaf (-9)) (.leaf (-10)))),
  (.branch 12 (.leaf (0)) (.branch 39 (.leaf (-2)) (.leaf (-3))))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 38 (.branch 20 (.leaf (-13)) (.branch 29 (.leaf (-12)) (.leaf (-11)))) (.branch 40 (.branch 39 (.leaf (-9)) (.leaf (-7))) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 41 (.leaf (-5)) (.leaf (-3))),
  (.branch 38 (.branch 36 (.leaf (-14)) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.branch 31 (.leaf (-3)) (.leaf (-2))) (.branch 33 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 34 (.branch 19 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_042_606 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (3))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (5)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (6)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_606
  counts := ![(.branch 20 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 10 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 17 (.leaf (7)) (.leaf (8)))))) (.branch 31 (.branch 24 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 38 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-4)) (.leaf (-5)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 39 (.leaf (-5)) (.leaf (-3))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_042_607 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (2))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (0))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (6)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (0)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (1)) (.leaf (0))) (.branch 24 (.leaf (1)) (.branch 25 (.leaf (4)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (3))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (5)) (.leaf (1))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (2)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (1)) (.leaf (6)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (3))))))))
  code := certificateD7_607
  counts := ![(.branch 20 (.branch 9 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 17 (.leaf (6)) (.leaf (7))))) (.branch 31 (.branch 26 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.leaf (15)))))),
  (.branch 22 (.branch 10 (.branch 5 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (2)) (.leaf (3)))) (.branch 16 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 19 (.leaf (6)) (.leaf (7))))) (.branch 33 (.branch 27 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 36 (.leaf (12)) (.leaf (13))) (.branch 41 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (2)))),
  (.branch 11 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2)))),
  (.branch 18 (.leaf (0)) (.branch 39 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-9)) (.leaf (-13)))),
  (.branch 2 (.leaf (0)) (.branch 10 (.leaf (-4)) (.leaf (-6)))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.leaf (-17))),
  (.branch 11 (.leaf (0)) (.leaf (-10))),
  (.branch 18 (.leaf (0)) (.leaf (-3)))]
  high := ![(.branch 35 (.branch 32 (.leaf (-13)) (.leaf (-12))) (.branch 38 (.leaf (-11)) (.branch 41 (.leaf (-10)) (.leaf (-5))))),
  (.branch 39 (.leaf (-6)) (.leaf (-5))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))]
def witnessD7_042_608 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (4)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (0)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (0))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (4)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (3)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (4)) (.leaf (2))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (0)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (2)) (.leaf (0))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (1)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (4)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (3)) (.leaf (2))))))))
  code := certificateD7_608
  counts := ![(.branch 18 (.branch 7 (.branch 1 (.leaf (0)) (.branch 3 (.leaf (1)) (.leaf (2)))) (.branch 12 (.branch 9 (.leaf (3)) (.leaf (4))) (.branch 15 (.leaf (5)) (.leaf (6))))) (.branch 30 (.branch 24 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 36 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 39 (.leaf (13)) (.leaf (14)))))),
  (.branch 19 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 21 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 32 (.branch 26 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.branch 42 (.leaf (7)) (.leaf (8)))))),
  (.branch 20 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 3 (.leaf (-2)) (.leaf (-3)))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-11))) (.branch 10 (.leaf (-12)) (.branch 14 (.leaf (-13)) (.leaf (-14))))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-3)) (.leaf (-4)))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-11)))),
  (.branch 13 (.leaf (0)) (.leaf (-29))),
  (.branch 34 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.leaf (-14)) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 27 (.leaf (-1)) (.leaf (0))),
  (.branch 30 (.leaf (-4)) (.leaf (-3))),
  (.branch 39 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.branch 27 (.branch 20 (.branch 16 (.branch 14 (.leaf (-29)) (.branch 15 (.leaf (-28)) (.leaf (-27)))) (.branch 18 (.branch 17 (.leaf (-26)) (.leaf (-25))) (.branch 19 (.leaf (-24)) (.leaf (-23))))) (.branch 23 (.branch 21 (.leaf (-22)) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_042_609 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (5)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (6))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (5)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (6)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (3)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (6)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (4))))))))
  code := certificateD7_609
  counts := ![(.branch 19 (.branch 8 (.branch 3 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 5 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 16 (.leaf (6)) (.leaf (7))))) (.branch 29 (.branch 24 (.branch 22 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (10)) (.leaf (11)))) (.branch 34 (.branch 32 (.leaf (12)) (.leaf (13))) (.branch 37 (.leaf (14)) (.branch 40 (.leaf (15)) (.leaf (16))))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 30 (.leaf (2)) (.branch 41 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 35 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 14 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 3 (.branch 1 (.leaf (0)) (.leaf (-5))) (.branch 5 (.leaf (-7)) (.branch 26 (.leaf (-9)) (.leaf (-10))))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-10)))) (.branch 18 (.leaf (-11)) (.branch 39 (.leaf (-13)) (.leaf (-14))))),
  (.branch 9 (.leaf (0)) (.leaf (-3))),
  (.branch 7 (.leaf (0)) (.leaf (-7))),
  (.leaf (0)),
  (.branch 4 (.leaf (0)) (.branch 17 (.leaf (-11)) (.leaf (-13)))),
  (.branch 25 (.branch 12 (.leaf (0)) (.leaf (-3))) (.branch 38 (.leaf (-5)) (.leaf (-7))))]
  high := ![(.branch 38 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-5)))),
  (.branch 40 (.leaf (-14)) (.branch 41 (.leaf (-10)) (.leaf (-6)))),
  (.branch 31 (.leaf (-3)) (.leaf (-2))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0)),
  (.branch 37 (.branch 34 (.branch 18 (.leaf (-13)) (.leaf (-12))) (.branch 35 (.leaf (-11)) (.branch 36 (.leaf (-10)) (.leaf (-9))))) (.branch 39 (.branch 38 (.leaf (-8)) (.leaf (-7))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4)))))),
  (.branch 40 (.branch 39 (.leaf (-7)) (.leaf (-6))) (.branch 41 (.leaf (-5)) (.leaf (-4))))]
def witnessD7_042_610 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (3)) (.leaf (2))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (4)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (6)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (2)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (4)) (.leaf (3))))))))
  code := certificateD7_610
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.branch 14 (.leaf (1)) (.leaf (2)))) (.branch 35 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (2)))),
  (.branch 10 (.leaf (0)) (.leaf (1))),
  (.branch 31 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 7 (.leaf (-3)) (.leaf (-5)))) (.branch 28 (.leaf (-7)) (.branch 38 (.leaf (-8)) (.leaf (-10))))),
  (.branch 6 (.leaf (0)) (.leaf (-1))),
  (.branch 20 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-32))),
  (.branch 31 (.leaf (0)) (.leaf (-11)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 40 (.branch 39 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.leaf (-1)),
  (.branch 26 (.branch 18 (.branch 14 (.branch 12 (.branch 11 (.leaf (-32)) (.leaf (-31))) (.branch 13 (.leaf (-30)) (.leaf (-29)))) (.branch 16 (.branch 15 (.leaf (-28)) (.leaf (-27))) (.branch 17 (.leaf (-26)) (.leaf (-25))))) (.branch 22 (.branch 20 (.branch 19 (.leaf (-24)) (.leaf (-23))) (.branch 21 (.leaf (-22)) (.leaf (-21)))) (.branch 24 (.branch 23 (.leaf (-20)) (.leaf (-19))) (.branch 25 (.leaf (-18)) (.leaf (-17)))))) (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_042_611 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (1))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (5)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (6)) (.leaf (0))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (3)) (.leaf (1))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (2)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (0)) (.leaf (6))))))))
  code := certificateD7_611
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 27 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 41 (.leaf (14)) (.leaf (15)))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 25 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 22 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 36 (.leaf (2)) (.leaf (3)))),
  (.branch 6 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (1)) (.leaf (2)))),
  (.branch 20 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 8 (.leaf (0)) (.leaf (-6))),
  (.branch 6 (.leaf (0)) (.leaf (-15))),
  (.branch 14 (.leaf (0)) (.branch 34 (.leaf (-7)) (.leaf (-8)))),
  (.branch 20 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 33 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 40 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 30 (.branch 7 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 21 (.leaf (-1)) (.leaf (0)))]
def witnessD7_042_612 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (1))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (5)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (1))))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (3))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_612
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 9 (.branch 2 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 14 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 17 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 28 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 5 (.leaf (-3)) (.leaf (-4)))),
  (.branch 3 (.leaf (0)) (.leaf (-15))),
  (.branch 7 (.leaf (0)) (.branch 17 (.leaf (-7)) (.leaf (-8)))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.leaf (-4)) (.leaf (-2))),
  (.branch 38 (.branch 36 (.branch 25 (.leaf (-15)) (.leaf (-14))) (.branch 37 (.leaf (-12)) (.leaf (-10)))) (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 40 (.branch 39 (.leaf (-8)) (.leaf (-6))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_042_613 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (0)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (3)) (.branch 14 (.leaf (5)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (0)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (0))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (5))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (6))))))))
  code := certificateD7_613
  counts := ![(.branch 20 (.branch 9 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 12 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 26 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 37 (.branch 34 (.leaf (12)) (.leaf (13))) (.branch 40 (.leaf (14)) (.leaf (15)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 35 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 13 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 27 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (1)) (.leaf (2)))),
  (.branch 14 (.leaf (0)) (.branch 36 (.leaf (1)) (.leaf (2)))),
  (.branch 22 (.leaf (0)) (.branch 42 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 6 (.leaf (-9)) (.leaf (-12)))),
  (.branch 2 (.leaf (0)) (.branch 11 (.leaf (-8)) (.leaf (-9)))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 8 (.leaf (0)) (.branch 28 (.leaf (-13)) (.leaf (-14)))),
  (.branch 14 (.leaf (0)) (.leaf (-7))),
  (.leaf (0))]
  high := ![(.branch 38 (.branch 35 (.leaf (-12)) (.leaf (-11))) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.branch 35 (.branch 31 (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))) (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.leaf (-8))))) (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 38 (.branch 15 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (0))]
def witnessD7_042_614 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (4)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (3)) (.branch 20 (.leaf (1)) (.leaf (0))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (5))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (6)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (3)) (.branch 41 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_614
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 27 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 41 (.leaf (14)) (.leaf (15)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 19 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 40 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 23 (.leaf (0)) (.leaf (1))),
  (.branch 37 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.leaf (-4)))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.branch 9 (.leaf (0)) (.leaf (-33))),
  (.branch 23 (.leaf (0)) (.leaf (-19))),
  (.branch 37 (.leaf (0)) (.leaf (-5)))]
  high := ![(.branch 33 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 40 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 40 (.leaf (-1)) (.leaf (0))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 15 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 16 (.leaf (-27)) (.leaf (-26))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.leaf (-18)))))) (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 32 (.branch 27 (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))) (.branch 29 (.branch 28 (.leaf (-15)) (.leaf (-14))) (.branch 30 (.leaf (-13)) (.branch 31 (.leaf (-12)) (.leaf (-11)))))) (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_042_615 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (1)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (2)) (.leaf (6))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (3))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (0)) (.leaf (2)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (1)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (4)) (.branch 30 (.leaf (1)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (3))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (0)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (1)) (.leaf (4))))))))
  code := certificateD7_615
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 17 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 25 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 38 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 40 (.leaf (13)) (.leaf (14)))))),
  (.branch 20 (.branch 9 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (1)) (.leaf (2)))) (.branch 13 (.leaf (3)) (.branch 16 (.leaf (4)) (.leaf (5))))) (.branch 30 (.branch 23 (.leaf (6)) (.branch 27 (.leaf (7)) (.leaf (8)))) (.branch 37 (.branch 34 (.leaf (9)) (.leaf (10))) (.branch 41 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 3 (.leaf (0)) (.branch 11 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 15 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 36 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 33 (.leaf (0)) (.leaf (1))),
  (.branch 12 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 2 (.leaf (0)) (.leaf (-3))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.branch 15 (.leaf (-11)) (.leaf (-12)))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-4)) (.leaf (-7)))),
  (.branch 33 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-30)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.leaf (-3)) (.leaf (-2))),
  (.branch 40 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 37 (.leaf (-12)) (.branch 38 (.leaf (-10)) (.leaf (-8)))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 35 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 36 (.leaf (-1)) (.leaf (0))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.branch 19 (.branch 15 (.branch 13 (.leaf (-30)) (.branch 14 (.leaf (-29)) (.leaf (-28)))) (.branch 17 (.branch 16 (.leaf (-27)) (.leaf (-26))) (.branch 18 (.leaf (-25)) (.leaf (-24))))) (.branch 23 (.branch 21 (.branch 20 (.leaf (-23)) (.leaf (-22))) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))]
def witnessD7_042_616 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (3))) (.branch 13 (.leaf (1)) (.branch 14 (.leaf (0)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (3)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (4))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (6)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (4))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (3)) (.leaf (4))))))))
  code := certificateD7_616
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 14 (.branch 11 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 32 (.branch 25 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 29 (.leaf (9)) (.leaf (10)))) (.branch 37 (.branch 35 (.leaf (11)) (.leaf (12))) (.branch 40 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 27 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 39 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 26 (.leaf (3)) (.leaf (4))) (.branch 41 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.branch 15 (.leaf (1)) (.leaf (2)))) (.branch 36 (.branch 28 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 9 (.leaf (0)) (.leaf (1))),
  (.branch 30 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-4))) (.branch 23 (.leaf (-6)) (.branch 27 (.leaf (-7)) (.leaf (-9))))),
  (.branch 3 (.leaf (0)) (.leaf (-4))),
  (.branch 5 (.leaf (0)) (.leaf (-2))),
  (.leaf (0)),
  (.branch 9 (.leaf (0)) (.leaf (-33))),
  (.branch 30 (.leaf (0)) (.leaf (-12)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7)))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 34 (.leaf (-2)) (.leaf (-1))),
  (.leaf (0)),
  (.branch 25 (.branch 17 (.branch 13 (.branch 11 (.branch 10 (.leaf (-33)) (.leaf (-32))) (.branch 12 (.leaf (-31)) (.leaf (-30)))) (.branch 15 (.branch 14 (.leaf (-29)) (.leaf (-28))) (.branch 16 (.leaf (-27)) (.leaf (-26))))) (.branch 21 (.branch 19 (.branch 18 (.leaf (-25)) (.leaf (-24))) (.branch 20 (.leaf (-23)) (.leaf (-22)))) (.branch 23 (.branch 22 (.leaf (-21)) (.leaf (-20))) (.branch 24 (.leaf (-19)) (.leaf (-18)))))) (.branch 33 (.branch 29 (.branch 27 (.branch 26 (.leaf (-17)) (.leaf (-16))) (.branch 28 (.leaf (-15)) (.leaf (-14)))) (.branch 31 (.branch 30 (.leaf (-13)) (.leaf (-12))) (.branch 32 (.leaf (-11)) (.leaf (-10))))) (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_042_617 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (2)) (.branch 20 (.leaf (5)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (3))))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (4)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (2)) (.branch 41 (.leaf (6)) (.leaf (4))))))))
  code := certificateD7_617
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 17 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.leaf (3)))) (.branch 28 (.branch 23 (.leaf (4)) (.leaf (5))) (.branch 33 (.leaf (6)) (.branch 38 (.leaf (7)) (.leaf (8)))))),
  (.branch 19 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 40 (.leaf (7)) (.leaf (8)))))),
  (.branch 16 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 37 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 7 (.branch 2 (.leaf (0)) (.leaf (-13))) (.branch 12 (.leaf (-14)) (.branch 17 (.leaf (-15)) (.leaf (-16))))),
  (.branch 3 (.leaf (0)) (.leaf (-9))),
  (.branch 5 (.leaf (0)) (.leaf (-11))),
  (.branch 10 (.leaf (0)) (.leaf (-1))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 40 (.branch 39 (.leaf (-16)) (.leaf (-12))) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 25 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-4)))),
  (.branch 39 (.branch 27 (.leaf (-11)) (.branch 38 (.leaf (-10)) (.leaf (-8)))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 32 (.leaf (-1)) (.leaf (0))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_042_618 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (0))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (5)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (3))) (.branch 24 (.leaf (4)) (.branch 25 (.leaf (1)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (6)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (3)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (2))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (3)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (4)) (.leaf (2)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_618
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 31 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 37 (.leaf (6)) (.leaf (7))))),
  (.branch 21 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 16 (.leaf (2)) (.leaf (3)))) (.branch 33 (.branch 28 (.leaf (4)) (.leaf (5))) (.branch 39 (.leaf (6)) (.leaf (7))))),
  (.branch 23 (.branch 11 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 17 (.leaf (2)) (.leaf (3)))) (.branch 35 (.branch 30 (.leaf (4)) (.leaf (5))) (.branch 42 (.leaf (6)) (.leaf (7))))),
  (.branch 24 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 38 (.leaf (2)) (.leaf (3)))),
  (.branch 20 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 2 (.leaf (0)) (.branch 7 (.leaf (-4)) (.leaf (-5)))),
  (.branch 3 (.leaf (0)) (.leaf (-3))),
  (.branch 5 (.leaf (0)) (.leaf (-1))),
  (.branch 10 (.leaf (0)) (.leaf (-4))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 37 (.branch 33 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 36 (.leaf (-1)) (.leaf (0))),
  (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.leaf (-1))]
def witnessD7_042_619 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (3))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (5)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (2))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (1)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (0)) (.leaf (2))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (5)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (2)) (.branch 38 (.leaf (1)) (.leaf (0)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (3))))))))
  code := certificateD7_619
  counts := ![(.branch 20 (.branch 8 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 6 (.leaf (2)) (.leaf (3)))) (.branch 13 (.branch 11 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (6)) (.branch 18 (.leaf (7)) (.leaf (8)))))) (.branch 32 (.branch 25 (.branch 22 (.leaf (9)) (.leaf (10))) (.branch 27 (.leaf (11)) (.branch 29 (.leaf (12)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (14)) (.leaf (15))) (.branch 39 (.leaf (16)) (.branch 41 (.leaf (17)) (.leaf (18))))))),
  (.branch 17 (.branch 2 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 23 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 3 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 28 (.leaf (3)) (.branch 37 (.leaf (4)) (.leaf (5))))),
  (.branch 24 (.branch 7 (.leaf (0)) (.branch 16 (.leaf (1)) (.leaf (2)))) (.branch 33 (.leaf (3)) (.branch 42 (.leaf (4)) (.leaf (5))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 9 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-4))),
  (.branch 2 (.leaf (0)) (.leaf (-5))),
  (.branch 3 (.leaf (0)) (.branch 28 (.leaf (-11)) (.leaf (-12)))),
  (.branch 7 (.leaf (0)) (.leaf (-3))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 35 (.leaf (-8)) (.leaf (-9)))),
  (.branch 9 (.leaf (0)) (.leaf (-12))),
  (.branch 19 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 37 (.leaf (-4)) (.leaf (-3))),
  (.branch 39 (.branch 24 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 39 (.branch 29 (.leaf (-12)) (.branch 38 (.leaf (-11)) (.leaf (-9)))) (.branch 40 (.leaf (-7)) (.branch 41 (.leaf (-5)) (.leaf (-3))))),
  (.branch 25 (.leaf (-3)) (.branch 34 (.leaf (-2)) (.leaf (0)))),
  (.branch 38 (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))) (.branch 40 (.branch 39 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.branch 36 (.branch 33 (.branch 31 (.leaf (-12)) (.branch 32 (.leaf (-11)) (.leaf (-10)))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_042_620 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (2)) (.branch 9 (.leaf (3)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (2)) (.leaf (0)))) (.branch 19 (.leaf (6)) (.branch 20 (.leaf (1)) (.leaf (0))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (2)) (.leaf (3))) (.branch 24 (.leaf (0)) (.branch 25 (.leaf (1)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (0)) (.leaf (2))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (1)) (.leaf (2)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (5))) (.branch 34 (.leaf (1)) (.branch 35 (.leaf (0)) (.leaf (2))))) (.branch 39 (.branch 37 (.leaf (3)) (.branch 38 (.leaf (0)) (.leaf (1)))) (.branch 40 (.leaf (6)) (.branch 41 (.leaf (0)) (.leaf (2))))))))
  code := certificateD7_620
  counts := ![(.branch 21 (.branch 10 (.branch 4 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 7 (.leaf (2)) (.leaf (3)))) (.branch 15 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 18 (.leaf (6)) (.leaf (7))))) (.branch 32 (.branch 27 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 38 (.branch 35 (.leaf (12)) (.leaf (13))) (.branch 41 (.leaf (14)) (.leaf (15)))))),
  (.branch 20 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 30 (.branch 25 (.leaf (5)) (.leaf (6))) (.branch 34 (.leaf (7)) (.branch 39 (.leaf (8)) (.leaf (9)))))),
  (.branch 22 (.branch 8 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.branch 17 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 28 (.leaf (5)) (.leaf (6))) (.branch 36 (.leaf (7)) (.branch 42 (.leaf (8)) (.leaf (9)))))),
  (.branch 23 (.branch 9 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2)))),
  (.branch 12 (.leaf (0)) (.branch 33 (.leaf (1)) (.leaf (2)))),
  (.branch 19 (.leaf (0)) (.branch 40 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-9))),
  (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-8)) (.leaf (-10)))),
  (.branch 17 (.branch 3 (.leaf (0)) (.leaf (-2))) (.branch 31 (.leaf (-3)) (.leaf (-4)))),
  (.branch 9 (.leaf (0)) (.leaf (-5))),
  (.branch 5 (.leaf (0)) (.leaf (-16))),
  (.branch 12 (.leaf (0)) (.leaf (-9))),
  (.branch 19 (.leaf (0)) (.leaf (-2)))]
  high := ![(.branch 33 (.branch 30 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.branch 39 (.leaf (-6)) (.leaf (-5))))),
  (.branch 40 (.branch 35 (.leaf (-10)) (.leaf (-9))) (.branch 41 (.leaf (-6)) (.leaf (-3)))),
  (.branch 38 (.branch 37 (.leaf (-4)) (.leaf (-3))) (.branch 39 (.leaf (-2)) (.branch 40 (.leaf (-1)) (.leaf (0))))),
  (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 41 (.leaf (-2)) (.leaf (-1)))]
def witnessD7_042_621 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (3))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (4)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (5)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (4))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (2)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (3))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (4)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (6)) (.leaf (3))))))))
  code := certificateD7_621
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 31 (.branch 25 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 37 (.branch 34 (.leaf (11)) (.leaf (12))) (.branch 40 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.branch 12 (.leaf (1)) (.leaf (2)))) (.branch 33 (.branch 29 (.leaf (3)) (.leaf (4))) (.branch 42 (.leaf (5)) (.leaf (6))))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 26 (.leaf (2)) (.branch 35 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.leaf (0)) (.leaf (1))),
  (.branch 41 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.branch 39 (.leaf (-11)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 12 (.leaf (0)) (.branch 33 (.leaf (-4)) (.leaf (-7)))),
  (.branch 14 (.branch 5 (.leaf (0)) (.leaf (-6))) (.branch 35 (.leaf (-8)) (.leaf (-9)))),
  (.branch 20 (.leaf (0)) (.leaf (-22))),
  (.branch 41 (.leaf (0)) (.leaf (-1)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 39 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-7)) (.leaf (-6))) (.branch 36 (.leaf (-5)) (.leaf (-4)))) (.branch 39 (.branch 38 (.leaf (-3)) (.leaf (-2))) (.branch 40 (.leaf (-1)) (.leaf (0))))),
  (.branch 38 (.branch 36 (.leaf (-9)) (.branch 37 (.leaf (-8)) (.leaf (-7)))) (.branch 40 (.branch 39 (.leaf (-6)) (.leaf (-5))) (.branch 41 (.leaf (-4)) (.leaf (-3))))),
  (.branch 31 (.branch 25 (.branch 22 (.branch 21 (.leaf (-22)) (.leaf (-21))) (.branch 23 (.leaf (-20)) (.branch 24 (.leaf (-19)) (.leaf (-18))))) (.branch 28 (.branch 26 (.leaf (-17)) (.branch 27 (.leaf (-16)) (.leaf (-15)))) (.branch 29 (.leaf (-14)) (.branch 30 (.leaf (-13)) (.leaf (-12)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (-11)) (.leaf (-10))) (.branch 34 (.leaf (-9)) (.branch 35 (.leaf (-8)) (.leaf (-7))))) (.branch 39 (.branch 37 (.leaf (-6)) (.branch 38 (.leaf (-5)) (.leaf (-4)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.leaf (-1))]
def witnessD7_042_622 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (0))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (2)) (.leaf (0)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (5))) (.branch 13 (.leaf (0)) (.branch 14 (.leaf (6)) (.leaf (1))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (2)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (4)) (.leaf (3))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (5))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (0))) (.branch 29 (.leaf (3)) (.branch 30 (.leaf (2)) (.leaf (0)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (4))) (.branch 34 (.leaf (0)) (.branch 35 (.leaf (6)) (.leaf (1))))) (.branch 39 (.branch 37 (.leaf (0)) (.branch 38 (.leaf (2)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (5)) (.leaf (3))))))))
  code := certificateD7_622
  counts := ![(.branch 19 (.branch 7 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 13 (.branch 10 (.leaf (3)) (.leaf (4))) (.branch 16 (.leaf (5)) (.leaf (6))))) (.branch 31 (.branch 25 (.branch 22 (.leaf (7)) (.leaf (8))) (.branch 28 (.leaf (9)) (.leaf (10)))) (.branch 37 (.branch 34 (.leaf (11)) (.leaf (12))) (.branch 40 (.leaf (13)) (.leaf (14)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 15 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 36 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 17 (.branch 3 (.leaf (0)) (.branch 9 (.leaf (1)) (.leaf (2)))) (.branch 30 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 38 (.leaf (5)) (.leaf (6))))),
  (.branch 21 (.branch 8 (.leaf (0)) (.leaf (1))) (.branch 29 (.leaf (2)) (.branch 42 (.leaf (3)) (.leaf (4))))),
  (.branch 20 (.branch 5 (.leaf (0)) (.leaf (1))) (.branch 33 (.leaf (2)) (.leaf (3)))),
  (.branch 26 (.branch 12 (.leaf (0)) (.leaf (1))) (.branch 41 (.leaf (2)) (.leaf (3)))),
  (.branch 14 (.leaf (0)) (.branch 35 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-2))),
  (.branch 6 (.branch 2 (.leaf (0)) (.leaf (-7))) (.branch 18 (.leaf (-8)) (.branch 39 (.leaf (-11)) (.leaf (-13))))),
  (.branch 3 (.leaf (0)) (.branch 9 (.leaf (-4)) (.leaf (-5)))),
  (.branch 8 (.leaf (0)) (.branch 29 (.leaf (-4)) (.leaf (-7)))),
  (.branch 5 (.leaf (0)) (.leaf (-9))),
  (.branch 12 (.leaf (0)) (.leaf (-2))),
  (.branch 14 (.leaf (0)) (.leaf (-7)))]
  high := ![(.branch 41 (.leaf (-2)) (.leaf (-1))),
  (.branch 40 (.leaf (-13)) (.branch 41 (.leaf (-10)) (.leaf (-7)))),
  (.branch 39 (.branch 31 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 33 (.branch 31 (.branch 30 (.leaf (-7)) (.leaf (-6))) (.branch 32 (.leaf (-5)) (.leaf (-4)))) (.branch 35 (.branch 34 (.leaf (-3)) (.leaf (-2))) (.branch 36 (.leaf (-1)) (.leaf (0))))),
  (.branch 37 (.branch 35 (.branch 34 (.leaf (-9)) (.leaf (-8))) (.branch 36 (.leaf (-7)) (.leaf (-6)))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1)))))),
  (.branch 27 (.leaf (-2)) (.leaf (-1))),
  (.branch 38 (.branch 36 (.leaf (-7)) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_042_623 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (3)) (.leaf (0)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (2)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (0)) (.leaf (6))))) (.branch 28 (.branch 27 (.leaf (5)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (3)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (4)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (3)) (.leaf (0)))) (.branch 40 (.leaf (1)) (.branch 41 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_623
  counts := ![(.branch 18 (.branch 8 (.branch 1 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (2)))) (.branch 11 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 25 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 32 (.leaf (9)) (.leaf (10))) (.branch 39 (.leaf (11)) (.leaf (12)))))),
  (.branch 19 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 12 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 33 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 40 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (1))) (.branch 31 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 34 (.leaf (2)) (.leaf (3)))),
  (.branch 27 (.branch 13 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 5 (.leaf (0)) (.branch 26 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.branch 4 (.leaf (-5)) (.leaf (-6)))),
  (.branch 19 (.branch 2 (.leaf (0)) (.leaf (-5))) (.branch 23 (.leaf (-7)) (.branch 40 (.leaf (-8)) (.leaf (-10))))),
  (.branch 3 (.leaf (0)) (.branch 24 (.leaf (-7)) (.leaf (-8)))),
  (.branch 17 (.branch 10 (.leaf (0)) (.leaf (-3))) (.branch 38 (.leaf (-9)) (.leaf (-14)))),
  (.branch 6 (.leaf (0)) (.leaf (-8))),
  (.branch 13 (.leaf (0)) (.leaf (-1))),
  (.branch 5 (.leaf (0)) (.leaf (-16)))]
  high := ![(.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 41 (.leaf (-10)) (.leaf (-8))),
  (.branch 25 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-5)))),
  (.branch 40 (.branch 39 (.leaf (-14)) (.leaf (-13))) (.branch 41 (.leaf (-12)) (.leaf (-11)))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))),
  (.branch 28 (.leaf (-1)) (.leaf (0))),
  (.branch 34 (.branch 30 (.branch 28 (.branch 27 (.leaf (-16)) (.leaf (-15))) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_042_624 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (4))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (1)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (6)) (.leaf (0))) (.branch 13 (.leaf (2)) (.branch 14 (.leaf (1)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (3)) (.leaf (1)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (4))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (2)) (.branch 25 (.leaf (3)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (1)) (.leaf (5))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (1)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (6)) (.leaf (0))) (.branch 34 (.leaf (2)) (.branch 35 (.leaf (1)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (4)) (.branch 38 (.leaf (3)) (.leaf (1)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (5))))))))
  code := certificateD7_624
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 18 (.branch 6 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 10 (.leaf (2)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 31 (.branch 23 (.leaf (5)) (.branch 27 (.leaf (6)) (.leaf (7)))) (.branch 35 (.leaf (8)) (.branch 39 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 13 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 24 (.leaf (4)) (.leaf (5))) (.branch 34 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 17 (.branch 4 (.leaf (0)) (.leaf (1))) (.branch 25 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 21 (.branch 7 (.leaf (0)) (.leaf (1))) (.branch 37 (.leaf (2)) (.leaf (3)))),
  (.branch 28 (.branch 16 (.leaf (0)) (.leaf (1))) (.branch 42 (.leaf (2)) (.leaf (3)))),
  (.branch 11 (.leaf (0)) (.branch 32 (.leaf (1)) (.leaf (2))))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 10 (.branch 2 (.leaf (0)) (.branch 6 (.leaf (-11)) (.leaf (-12)))) (.branch 14 (.leaf (-13)) (.branch 18 (.leaf (-14)) (.leaf (-15))))),
  (.branch 13 (.branch 3 (.leaf (0)) (.leaf (-3))) (.branch 24 (.leaf (-5)) (.branch 34 (.leaf (-6)) (.leaf (-8))))),
  (.branch 4 (.leaf (0)) (.branch 25 (.leaf (-8)) (.leaf (-11)))),
  (.branch 7 (.leaf (0)) (.branch 21 (.leaf (-8)) (.leaf (-9)))),
  (.branch 28 (.leaf (0)) (.leaf (-2))),
  (.branch 11 (.leaf (0)) (.leaf (-10)))]
  high := ![(.branch 37 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 40 (.leaf (-15)) (.branch 41 (.leaf (-10)) (.leaf (-5)))),
  (.branch 35 (.leaf (-8)) (.leaf (-7))),
  (.branch 39 (.branch 26 (.leaf (-11)) (.leaf (-10))) (.branch 40 (.leaf (-9)) (.branch 41 (.leaf (-8)) (.leaf (-7))))),
  (.branch 39 (.branch 22 (.leaf (-9)) (.branch 38 (.leaf (-8)) (.leaf (-7)))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-5)) (.leaf (-4))))),
  (.branch 29 (.leaf (-2)) (.branch 30 (.leaf (-1)) (.leaf (0)))),
  (.branch 37 (.branch 34 (.branch 33 (.leaf (-10)) (.leaf (-9))) (.branch 35 (.leaf (-8)) (.branch 36 (.leaf (-7)) (.leaf (-6))))) (.branch 39 (.branch 38 (.leaf (-5)) (.leaf (-4))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-2)) (.leaf (-1))))))]
def witnessD7_042_625 : CycleWitness 7 where
  length := 42
  word := (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (0))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (1))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (2)) (.leaf (3)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (1)) (.leaf (0))) (.branch 13 (.leaf (5)) (.branch 14 (.leaf (2)) (.leaf (0))))) (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (4)) (.leaf (3)))) (.branch 19 (.leaf (0)) (.branch 20 (.leaf (2)) (.leaf (1))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (0)) (.leaf (1))) (.branch 24 (.leaf (3)) (.branch 25 (.leaf (2)) (.leaf (0))))) (.branch 28 (.branch 27 (.leaf (4)) (.leaf (1))) (.branch 29 (.leaf (0)) (.branch 30 (.leaf (2)) (.leaf (3)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (1)) (.leaf (0))) (.branch 34 (.leaf (6)) (.branch 35 (.leaf (2)) (.leaf (0))))) (.branch 39 (.branch 37 (.leaf (1)) (.branch 38 (.leaf (4)) (.leaf (3)))) (.branch 40 (.leaf (0)) (.branch 41 (.leaf (2)) (.leaf (1))))))))
  code := certificateD7_625
  counts := ![(.branch 19 (.branch 8 (.branch 1 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (2)))) (.branch 12 (.leaf (3)) (.branch 15 (.leaf (4)) (.leaf (5))))) (.branch 29 (.branch 22 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 36 (.branch 33 (.leaf (9)) (.leaf (10))) (.branch 40 (.leaf (11)) (.leaf (12)))))),
  (.branch 21 (.branch 7 (.branch 2 (.leaf (0)) (.leaf (1))) (.branch 11 (.leaf (2)) (.branch 16 (.leaf (3)) (.leaf (4))))) (.branch 32 (.branch 23 (.leaf (5)) (.branch 28 (.leaf (6)) (.leaf (7)))) (.branch 37 (.leaf (8)) (.branch 42 (.leaf (9)) (.leaf (10)))))),
  (.branch 20 (.branch 9 (.branch 3 (.leaf (0)) (.leaf (1))) (.branch 14 (.leaf (2)) (.leaf (3)))) (.branch 30 (.branch 25 (.leaf (4)) (.leaf (5))) (.branch 35 (.leaf (6)) (.branch 41 (.leaf (7)) (.leaf (8)))))),
  (.branch 18 (.branch 4 (.leaf (0)) (.branch 10 (.leaf (1)) (.leaf (2)))) (.branch 31 (.branch 24 (.leaf (3)) (.leaf (4))) (.branch 39 (.leaf (5)) (.leaf (6))))),
  (.branch 17 (.branch 6 (.leaf (0)) (.leaf (1))) (.branch 27 (.leaf (2)) (.branch 38 (.leaf (3)) (.leaf (4))))),
  (.branch 13 (.leaf (0)) (.leaf (1))),
  (.branch 34 (.leaf (0)) (.leaf (1)))]
  low := ![(.branch 1 (.leaf (0)) (.leaf (-5))),
  (.branch 2 (.leaf (0)) (.branch 23 (.leaf (-5)) (.leaf (-8)))),
  (.branch 3 (.leaf (0)) (.leaf (-7))),
  (.branch 4 (.leaf (0)) (.branch 10 (.leaf (-3)) (.leaf (-4)))),
  (.branch 6 (.leaf (0)) (.leaf (-9))),
  (.branch 13 (.leaf (0)) (.leaf (-29))),
  (.branch 34 (.leaf (0)) (.leaf (-8)))]
  high := ![(.branch 37 (.leaf (-5)) (.branch 41 (.leaf (-4)) (.leaf (-2)))),
  (.branch 39 (.branch 33 (.leaf (-8)) (.branch 38 (.leaf (-7)) (.leaf (-5)))) (.branch 40 (.leaf (-3)) (.branch 41 (.leaf (-1)) (.leaf (0))))),
  (.branch 36 (.leaf (-7)) (.leaf (-5))),
  (.branch 40 (.branch 32 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))),
  (.branch 39 (.branch 28 (.leaf (-9)) (.leaf (-8))) (.branch 40 (.leaf (-6)) (.branch 41 (.leaf (-4)) (.leaf (-2))))),
  (.branch 27 (.branch 20 (.branch 16 (.branch 14 (.leaf (-29)) (.branch 15 (.leaf (-28)) (.leaf (-27)))) (.branch 18 (.branch 17 (.leaf (-26)) (.leaf (-25))) (.branch 19 (.leaf (-24)) (.leaf (-23))))) (.branch 23 (.branch 21 (.leaf (-22)) (.branch 22 (.leaf (-21)) (.leaf (-20)))) (.branch 25 (.branch 24 (.leaf (-19)) (.leaf (-18))) (.branch 26 (.leaf (-17)) (.leaf (-16)))))) (.branch 34 (.branch 30 (.branch 28 (.leaf (-15)) (.branch 29 (.leaf (-14)) (.leaf (-13)))) (.branch 32 (.branch 31 (.leaf (-12)) (.leaf (-11))) (.branch 33 (.leaf (-10)) (.leaf (-9))))) (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1))))))),
  (.branch 38 (.branch 36 (.branch 35 (.leaf (-8)) (.leaf (-7))) (.branch 37 (.leaf (-6)) (.leaf (-5)))) (.branch 40 (.branch 39 (.leaf (-4)) (.leaf (-3))) (.branch 41 (.leaf (-2)) (.leaf (-1)))))]
def witnessD7_042 : Fin 23 → CycleWitness 7 := ![witnessD7_042_603, witnessD7_042_604, witnessD7_042_605, witnessD7_042_606, witnessD7_042_607, witnessD7_042_608, witnessD7_042_609, witnessD7_042_610, witnessD7_042_611, witnessD7_042_612, witnessD7_042_613, witnessD7_042_614, witnessD7_042_615, witnessD7_042_616, witnessD7_042_617, witnessD7_042_618, witnessD7_042_619, witnessD7_042_620, witnessD7_042_621, witnessD7_042_622, witnessD7_042_623, witnessD7_042_624, witnessD7_042_625]
end RealPinwheel.FiveSixths


